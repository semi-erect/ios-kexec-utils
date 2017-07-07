/*
 * Copyright 2014, winocm. <winocm@icloud.com>
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *
 * $Id$
 */
/*
 * kloader
 * Requires: kernel patch for tfp0
 * Supports: iOS 4.0 and above (armv7 only)
 *
 * xcrun -sdk iphoneos clang kloader.c -arch armv7 -framework IOKit -framework CoreFoundation -Wall -miphoneos-version-min=4.0 -o kloader && ldid -Stfp0.plist kloader
 */

#include <mach/mach.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <CoreFoundation/CoreFoundation.h>
#include <sys/sysctl.h>
#include <signal.h>
#include <notify.h>
#include <mach-o/loader.h>

extern mach_port_t IOPMFindPowerManagement(mach_port_t);
extern kern_return_t IOPMSchedulePowerEvent(CFDateRef time_to_wake, CFStringRef my_id, CFStringRef type);
extern kern_return_t IOPMSleepSystem(mach_port_t);

/* ARM page bits for L1 sections */
#define L1_SHIFT             20  /* log2(1MB) */

#define L1_SECT_PROTO        (1 << 1)   /* 0b10 */

#define L1_SECT_B_BIT        (1 << 2)
#define L1_SECT_C_BIT        (1 << 3)

#define L1_SECT_SORDER       (0)    /* 0b00, not cacheable, strongly ordered */
#define L1_SECT_SH_DEVICE    (L1_SECT_B_BIT)
#define L1_SECT_WT_NWA       (L1_SECT_C_BIT)
#define L1_SECT_WB_NWA       (L1_SECT_B_BIT | L1_SECT_C_BIT)
#define L1_SECT_S_BIT        (1 << 16)

#define L1_SECT_AP_URW       (1 << 10) | (1 << 11)
#define L1_SECT_PFN(x)       (x & 0xFFF00000)

#define L1_SECT_DEFPROT      (L1_SECT_AP_URW)
#define L1_SECT_DEFCACHE     (L1_SECT_SORDER)

#define L1_PROTO_TTE(paddr)  (L1_SECT_PFN(paddr) | L1_SECT_S_BIT | L1_SECT_DEFPROT | L1_SECT_DEFCACHE | L1_SECT_PROTO)

#define PFN_SHIFT            2
#define TTB_OFFSET(vaddr)    ((vaddr >> L1_SHIFT) << PFN_SHIFT)

/*
 * Shadowmap begin and end. 15MB of shadowmap is enough for the kernel.
 * We don't need to invalidate unified D/I TLB or any cache lines
 * since the kernel is mapped as writethrough memory, and these
 * addresses are guaranteed to not be translated.
 * (Accesses will cause segmentation faults due to failure on L1 translation.)
 *
 * Clear the shadowmappings when done owning the kernel.
 *
 * 0x7ff0'0000 is also below the limit for vm_read and such, so that's also *great*.
 * (2048 bytes)
 */
#define SHADOWMAP_BEGIN          0x7f000000
#define SHADOWMAP_END            0x7ff00000
#define SHADOWMAP_GRANULARITY    0x00100000

#define SHADOWMAP_BEGIN_OFF     TTB_OFFSET(SHADOWMAP_BEGIN)
#define SHADOWMAP_END_OFF       TTB_OFFSET(SHADOWMAP_END)
#define SHADOWMAP_SIZE          (SHADOWMAP_END_OFF - SHADOWMAP_BEGIN_OFF)

#define TTB_SIZE                4096
#define DEFAULT_KERNEL_SLIDE    0x80000000
#define KERNEL_DUMP_SIZE        0xd00000
#define CHUNK_SIZE 2048

#define NOTIFY_STATUS_OK 0
#define kIOPMSystemPowerStateNotify "com.apple.powermanagement.systempowerstate"
#define kIOPMSettingDebugWakeRelativeKey "WakeRelativeToSleep"

static uint8_t kernel_dump[KERNEL_DUMP_SIZE + 0x1000] = {0};
static uint32_t ttb_template[TTB_SIZE] = {0};

typedef struct pmap_partial_t {
    uint32_t tte_virt;
    uint32_t tte_phys;
    /* ... */
} pmap_partial_t;

/* --- planetbeing patchfinder --- */

static uint32_t bit_range(uint32_t x, int start, int end) {
    x = (x << (31 - start)) >> (31 - start);
    x = (x >> end);
    return x;
}

static uint32_t ror(uint32_t x, int places) {
    return (x >> places) | (x << (32 - places));
}

static int thumb_expand_imm_c(uint16_t imm12) {
    if (bit_range(imm12, 11, 10) == 0) {
        switch (bit_range(imm12, 9, 8)) {
        case 0:
            return bit_range(imm12, 7, 0);
        case 1:
            return (bit_range(imm12, 7, 0) << 16) | bit_range(imm12, 7, 0);
        case 2:
            return (bit_range(imm12, 7, 0) << 24) | (bit_range(imm12, 7, 0) << 8);
        case 3:
            return (bit_range(imm12, 7, 0) << 24) | (bit_range(imm12, 7, 0) << 16) | (bit_range(imm12, 7, 0) << 8) | bit_range(imm12, 7, 0);
        default:
            return 0;
        }
    } else {
        uint32_t unrotated_value = 0x80 | bit_range(imm12, 6, 0);
        return ror(unrotated_value, bit_range(imm12, 11, 7));
    }
}

static int insn_is_32bit(uint16_t *i) {
    return (*i & 0xe000) == 0xe000 && (*i & 0x1800) != 0x0;
}

static int insn_is_bl(uint16_t *i) {
    if ((*i & 0xf800) == 0xf000 && (*(i + 1) & 0xd000) == 0xd000)
        return 1;
    else if ((*i & 0xf800) == 0xf000 && (*(i + 1) & 0xd001) == 0xc000)
        return 1;
    else
        return 0;
}

static uint32_t insn_bl_imm32(uint16_t *i) {
    uint16_t insn0 = *i;
    uint16_t insn1 = *(i + 1);
    uint32_t s = (insn0 >> 10) & 1;
    uint32_t j1 = (insn1 >> 13) & 1;
    uint32_t j2 = (insn1 >> 11) & 1;
    uint32_t i1 = ~(j1 ^ s) & 1;
    uint32_t i2 = ~(j2 ^ s) & 1;
    uint32_t imm10 = insn0 & 0x3ff;
    uint32_t imm11 = insn1 & 0x7ff;
    uint32_t imm32 = (imm11 << 1) | (imm10 << 12) | (i2 << 22) | (i1 << 23) | (s ? 0xff000000 : 0);
    return imm32;
}

static int insn_is_b_conditional(uint16_t *i) {
    return (*i & 0xF000) == 0xD000 && (*i & 0x0F00) != 0x0F00 && (*i & 0x0F00) != 0xE;
}

static int insn_is_b_unconditional(uint16_t *i) {
    if ((*i & 0xF800) == 0xE000)
        return 1;
    else if ((*i & 0xF800) == 0xF000 && (*(i + 1) & 0xD000) == 9)
        return 1;
    else
        return 0;
}

static int insn_is_ldr_literal(uint16_t *i) {
    return (*i & 0xF800) == 0x4800 || (*i & 0xFF7F) == 0xF85F;
}

static int insn_ldr_literal_rt(uint16_t *i) {
    if ((*i & 0xF800) == 0x4800)
        return (*i >> 8) & 7;
    else if ((*i & 0xFF7F) == 0xF85F)
        return (*(i + 1) >> 12) & 0xF;
    else
        return 0;
}

static int insn_ldr_literal_imm(uint16_t *i) {
    if ((*i & 0xF800) == 0x4800)
        return (*i & 0xF) << 2;
    else if ((*i & 0xFF7F) == 0xF85F)
        return (*(i + 1) & 0xFFF) * (((*i & 0x0800) == 0x0800) ? 1 : -1);
    else
        return 0;
}

static int insn_ldr_imm_rt(uint16_t *i) {
    return (*i & 7);
}

static int insn_ldr_imm_rn(uint16_t *i) {
    return ((*i >> 3) & 7);
}

static int insn_ldr_imm_imm(uint16_t *i) {
    return ((*i >> 6) & 0x1F);
}

static int insn_is_add_reg(uint16_t *i) {
    if ((*i & 0xFE00) == 0x1800)
        return 1;
    else if ((*i & 0xFF00) == 0x4400)
        return 1;
    else if ((*i & 0xFFE0) == 0xEB00)
        return 1;
    else
        return 0;
}

static int insn_add_reg_rd(uint16_t *i) {
    if ((*i & 0xFE00) == 0x1800)
        return (*i & 7);
    else if ((*i & 0xFF00) == 0x4400)
        return (*i & 7) | ((*i & 0x80) >> 4);
    else if ((*i & 0xFFE0) == 0xEB00)
        return (*(i + 1) >> 8) & 0xF;
    else
        return 0;
}

static int insn_add_reg_rn(uint16_t *i) {
    if ((*i & 0xFE00) == 0x1800)
        return ((*i >> 3) & 7);
    else if ((*i & 0xFF00) == 0x4400)
        return (*i & 7) | ((*i & 0x80) >> 4);
    else if ((*i & 0xFFE0) == 0xEB00)
        return (*i & 0xF);
    else
        return 0;
}

static int insn_add_reg_rm(uint16_t *i) {
    if ((*i & 0xFE00) == 0x1800)
        return (*i >> 6) & 7;
    else if ((*i & 0xFF00) == 0x4400)
        return (*i >> 3) & 0xF;
    else if ((*i & 0xFFE0) == 0xEB00)
        return *(i + 1) & 0xF;
    else
        return 0;
}

static int insn_is_movt(uint16_t *i) {
    return (*i & 0xFBF0) == 0xF2C0 && (*(i + 1) & 0x8000) == 0;
}

static int insn_movt_rd(uint16_t *i) {
    return (*(i + 1) >> 8) & 0xF;
}

static int insn_movt_imm(uint16_t *i) {
    return ((*i & 0xF) << 12) | ((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF);
}

static int insn_is_mov_imm(uint16_t *i) {
    if ((*i & 0xF800) == 0x2000)
        return 1;
    else if ((*i & 0xFBEF) == 0xF04F && (*(i + 1) & 0x8000) == 0)
        return 1;
    else if ((*i & 0xFBF0) == 0xF240 && (*(i + 1) & 0x8000) == 0)
        return 1;
    else
        return 0;
}

static int insn_mov_imm_rd(uint16_t *i) {
    if ((*i & 0xF800) == 0x2000)
        return (*i >> 8) & 7;
    else if ((*i & 0xFBEF) == 0xF04F && (*(i + 1) & 0x8000) == 0)
        return (*(i + 1) >> 8) & 0xF;
    else if ((*i & 0xFBF0) == 0xF240 && (*(i + 1) & 0x8000) == 0)
        return (*(i + 1) >> 8) & 0xF;
    else
        return 0;
}

static int insn_mov_imm_imm(uint16_t *i) {
    if ((*i & 0xF800) == 0x2000)
        return *i & 0xF;
    else if ((*i & 0xFBEF) == 0xF04F && (*(i + 1) & 0x8000) == 0)
        return thumb_expand_imm_c(((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF));
    else if ((*i & 0xFBF0) == 0xF240 && (*(i + 1) & 0x8000) == 0)
        return ((*i & 0xF) << 12) | ((*i & 0x0400) << 1) | ((*(i + 1) & 0x7000) >> 4) | (*(i + 1) & 0xFF);
    else
        return 0;
}

// Given an instruction, search backwards until an instruction is found matching the specified criterion.
static uint16_t *find_last_insn_matching(uint8_t *kdata, size_t ksize, uint16_t *current_instruction, int (*match_func) (uint16_t *)) {
    while ((uintptr_t) current_instruction > (uintptr_t) kdata) {
        if (insn_is_32bit(current_instruction - 2) && !insn_is_32bit(current_instruction - 3)) {
            current_instruction -= 2;
        } else {
            --current_instruction;
        }
        if (match_func(current_instruction)) {
            return current_instruction;
        }
    }
    return NULL;
}

// Given an instruction and a register, find the PC-relative address that was stored inside the register by the time the instruction was reached.
static uint32_t find_pc_rel_value(uint8_t *kdata, size_t ksize, uint16_t *insn, int reg) {
    // Find the last instruction that completely wiped out this register
    int found = 0;
    uint16_t *current_instruction = insn;
    while ((uintptr_t) current_instruction > (uintptr_t) kdata) {
        if (insn_is_32bit(current_instruction - 2)) {
            current_instruction -= 2;
        } else {
            --current_instruction;
        }

        if (insn_is_mov_imm(current_instruction) && insn_mov_imm_rd(current_instruction) == reg) {
            found = 1;
            break;
        }

        if (insn_is_ldr_literal(current_instruction) && insn_ldr_literal_rt(current_instruction) == reg) {
            found = 1;
            break;
        }
    }

    if (!found)
        return 0;

    // Step through instructions, executing them as a virtual machine, only caring about instructions that affect the target register and are commonly used for PC-relative addressing.
    uint32_t value = 0;
    while ((uintptr_t) current_instruction < (uintptr_t) insn) {
        if (insn_is_mov_imm(current_instruction) && insn_mov_imm_rd(current_instruction) == reg) {
            value = insn_mov_imm_imm(current_instruction);
        } else if (insn_is_ldr_literal(current_instruction) && insn_ldr_literal_rt(current_instruction) == reg) {
            value = *(uint32_t *) (kdata + (((((uintptr_t) current_instruction - (uintptr_t) kdata) + 4) & 0xFFFFFFFC) + insn_ldr_literal_imm(current_instruction)));
        } else if (insn_is_movt(current_instruction) && insn_movt_rd(current_instruction) == reg) {
            value |= insn_movt_imm(current_instruction) << 16;
        } else if (insn_is_add_reg(current_instruction) && insn_add_reg_rd(current_instruction) == reg) {
            if (insn_add_reg_rm(current_instruction) != 15 || insn_add_reg_rn(current_instruction) != reg) {
                // Can't handle this kind of operation!
                return 0;
            }
            value += ((uintptr_t) current_instruction - (uintptr_t) kdata) + 4;
        }
        current_instruction += insn_is_32bit(current_instruction) ? 2 : 1;
    }
    return value;
}

// Find PC-relative references to a certain address (relative to kdata). This is basically a virtual machine that only cares about instructions used in PC-relative addressing, so no branches, etc.
static uint16_t *find_literal_ref(uint8_t *kdata, size_t ksize, uint16_t *insn, uint32_t address) {
    uint16_t *current_instruction = insn;
    uint32_t value[16];
    memset(value, 0, sizeof(value));

    while ((uintptr_t) current_instruction < (uintptr_t) (kdata + ksize)) {
        if (insn_is_mov_imm(current_instruction)) {
            value[insn_mov_imm_rd(current_instruction)] = insn_mov_imm_imm(current_instruction);
        } else if (insn_is_ldr_literal(current_instruction)) {
            uintptr_t literal_address = (uintptr_t) kdata + ((((uintptr_t) current_instruction - (uintptr_t) kdata) + 4) & 0xFFFFFFFC) + insn_ldr_literal_imm(current_instruction);
            if (literal_address >= (uintptr_t) kdata && (literal_address + 4) <= ((uintptr_t) kdata + ksize)) {
                value[insn_ldr_literal_rt(current_instruction)] = *(uint32_t *) (literal_address);
            }
        } else if (insn_is_movt(current_instruction)) {
            value[insn_movt_rd(current_instruction)] |= insn_movt_imm(current_instruction) << 16;
        } else if (insn_is_add_reg(current_instruction)) {
            int reg = insn_add_reg_rd(current_instruction);
            if (insn_add_reg_rm(current_instruction) == 15 && insn_add_reg_rn(current_instruction) == reg) {
                value[reg] += ((uintptr_t) current_instruction - (uintptr_t) kdata) + 4;
                if (value[reg] == address) {
                    return current_instruction;
                }
            }
        }
        current_instruction += insn_is_32bit(current_instruction) ? 2 : 1;
    }
    return NULL;
}

static int find_macho_section(struct mach_header *hdr, size_t size, const char *segname, const char *sectname, uint32_t *ret_addr, uint32_t *ret_size) {
    /* Doesn't do bounds checking for size and other values */
    if (hdr->magic == MH_MAGIC) {
        struct load_command *cmd = (struct load_command *)(hdr + 1);
        for (int i = 0; i < hdr->ncmds; i++) {
            if (cmd->cmd == LC_SEGMENT) {
                struct segment_command *seg = (struct segment_command *)cmd;
                if (!strncmp(seg->segname, segname, 16)) {
                    for (uint32_t j = 0; j < seg->nsects; j++) {
                        struct section *sect = ((struct section *)(seg + 1)) + j;
                        if (!strncmp(sect->sectname, sectname, 16)) {
                            *ret_addr = sect->addr;
                            *ret_size = sect->size;
                            return 0;
                        }
                    }
                }
            }
            cmd = (struct load_command *)(((uint8_t *)cmd) + cmd->cmdsize);
        }
    }
    return 1;
}

/* Buggy, but re-implemented because some old versions of iOS don't have memmem */
static void * buggy_memmem(const void *haystack, size_t haystacklen, const void *needle, size_t needlelen) {
    if (haystack == NULL || haystacklen == 0 || needle == NULL || needlelen == 0) {
        printf("ERROR: Invalid arguments for buggy_memmem.\n");
        exit(1);
    }
    for (size_t i = 0; i < haystacklen; i++) {
        if (*(uint8_t *)(haystack + i) == *(uint8_t *)needle && i + needlelen <= haystacklen && 0 == memcmp(((uint8_t *)haystack) + i, needle, needlelen)) {
            return (void *)(((uint8_t *)haystack) + i);
        }
    }
    return NULL;
}

static uint32_t find_pmap_location_pre_iOS_6(uint32_t kernel_base, uint8_t *kdata, size_t ksize) {
    /* Find location of the pmap_map_bd string */
    uint8_t *pmap_map_bd = buggy_memmem(kdata, ksize, "\"pmap_map_bd\"", strlen("\"pmap_map_bd\""));
    if (NULL == pmap_map_bd) {
        printf("ERROR: Failed to find string \"pmap_map_bd\" in Mach-O.\n");
        exit(1);
    }

    /* Find xref to string "pmap_map_bd" (that function also references kernel_pmap) */
    uint32_t xref = 0;
    for (size_t i = 0; i < ksize; i += 4)
        if (*(uint32_t *)(kdata + i) == (uint32_t)(kernel_base + 0x1000 + pmap_map_bd - kdata)) {
            xref = i;
            break;
        }
    if (0 == xref) {
        printf("ERROR: Failed to find xref to string \"pmap_map_bd\" in Mach-O.\n");
        exit(1);
    }

    /* Find beginning of next function */
    uint32_t next_func_start = 0;
    for (int i = 0; i < 128; i += 2) {
        if (*(uint16_t *)(kdata + xref + i) == 0xB5F0) {
            /* Align to 4-byte boundary */
            next_func_start = (xref + i) & ~3;
            break;
        }
    }
    if (0 == next_func_start) {
        printf("ERROR: Failed to find next function within 128 bytes.\n");
        exit(1);
    }

    /* Find end of this function */
    uint32_t this_func_end = 0;
    for (int i = 0; i < 64; i += 2) {
        if (*(uint16_t *)(kdata + xref - i) == 0xBDF0) {
            /* Align to 4-byte boundary */
            this_func_end = (xref - i + 4) & ~3;
            break;
        }
    }
    if (0 == this_func_end) {
        printf("ERROR: Failed to find end of this function within 64 bytes.\n");
        exit(1);
    }

    uint32_t vm_addr = 0, vm_size = 0;
    /* Find location of __DATA __data section */
    if (0 != find_macho_section((struct mach_header *)kdata, ksize, SEG_DATA, SECT_DATA, &vm_addr, &vm_size)) {
        printf("ERROR: Failed to find __DATA __data in Mach-O header.\n");
        exit(1);
    }

    uint32_t pmap = 0;
    for (uint32_t *search = (uint32_t *)(kdata + this_func_end); search < (uint32_t *)(kdata + next_func_start); search += 1) {
        if (vm_addr <= *search && *search < vm_addr + vm_size) {
            if (pmap != 0 && pmap != *search) {
                printf("ERROR: Multiple possible values within __DATA __data section were found.\n");
                exit(1);
            }
            pmap = *search;
        }
    }
    if (0 == pmap) {
        printf("ERROR: No values within __DATA __data section were found.\n");
        exit(1);
    }

    return pmap - (kernel_base + 0x1000);
}

// This points to kernel_pmap. Use that to change the page tables if necessary.
static uint32_t find_pmap_location(uint8_t *kdata, size_t ksize) {
    // Find location of the pmap_map_bd string.
    uint8_t *pmap_map_bd = buggy_memmem(kdata, ksize, "\"pmap_map_bd\"", strlen("\"pmap_map_bd\""));
    if (!pmap_map_bd) {
        return 0;
    }

    // Find a reference to the pmap_map_bd string. That function also references kernel_pmap
    uint16_t *ptr = find_literal_ref(kdata, ksize, (uint16_t *)kdata, (uintptr_t)pmap_map_bd - (uintptr_t)kdata);
    if (!ptr) {
        return 0;
    }

    // Find the beginning of it (we may have a version that throws panic after the function end).
    while (*ptr != 0xB5F0) {
        if ((uint8_t *)ptr == kdata) {
            return 0;
        }
        ptr--;
    }

    // Find the end of it.
    const uint8_t search_function_end[] = { 0xF0, 0xBD };
    ptr = buggy_memmem(ptr, ksize - ((uintptr_t)ptr - (uintptr_t)kdata), search_function_end, sizeof(search_function_end));
    if (!ptr) {
        return 0;
    }

    // Find the last BL before the end of it. The third argument to it should be kernel_pmap
    uint16_t *bl = find_last_insn_matching(kdata, ksize, ptr, insn_is_bl);
    if (!bl) {
        return 0;
    }

    // Find the last LDR R2, [R*] before it that's before any branches. If there are branches, then we have a version of the function that assumes kernel_pmap instead of being passed it.
    uint16_t *ldr_r2 = NULL;
    uint16_t *current_instruction = bl;
    while ((uintptr_t) current_instruction > (uintptr_t) kdata) {
        if (insn_is_32bit(current_instruction - 2) && !insn_is_32bit(current_instruction - 3)) {
            current_instruction -= 2;
        } else {
            --current_instruction;
        }

        if (insn_ldr_imm_rt(current_instruction) == 2 && insn_ldr_imm_imm(current_instruction) == 0) {
            ldr_r2 = current_instruction;
            break;
        } else if (insn_is_b_conditional(current_instruction) || insn_is_b_unconditional(current_instruction)) {
            break;
        }
    }

    // The function has a third argument, which must be kernel_pmap. Find out its address
    if (ldr_r2) {
        return find_pc_rel_value(kdata, ksize, ldr_r2, insn_ldr_imm_rn(ldr_r2));
    }

    // The function has no third argument, Follow the BL.
    uint32_t imm32 = insn_bl_imm32(bl);
    uint32_t target = ((uintptr_t) bl - (uintptr_t) kdata) + 4 + imm32;
    if (target > ksize) {
        return 0;
    }

    // Find the first PC-relative reference in this function.
    current_instruction = (uint16_t *) (kdata + target);
    while ((uintptr_t) current_instruction < (uintptr_t) (kdata + ksize)) {
        if (insn_is_add_reg(current_instruction) && insn_add_reg_rm(current_instruction) == 15) {
            current_instruction += insn_is_32bit(current_instruction) ? 2 : 1;
            return find_pc_rel_value(kdata, ksize, current_instruction, insn_add_reg_rd(current_instruction));
        }
        current_instruction += insn_is_32bit(current_instruction) ? 2 : 1;
    }

    return 0;
}

static uint32_t find_larm_init_tramp(uint8_t *kdata, size_t ksize) {
    // ldr lr, [pc, lr];    b +0x0; cpsid if
    const uint8_t search[]  = { 0x0E, 0xE0, 0x9F, 0xE7, 0xFF, 0xFF, 0xFF, 0xEA, 0xC0, 0x00, 0x0C, 0xF1 };
    void *ptr = buggy_memmem(kdata, ksize, search, sizeof(search));
    if (ptr) {
      return ((uintptr_t)ptr) - ((uintptr_t)kdata);
    }

    // ldr lr, [pc #value]; b +0x0; cpsid if
    const uint8_t search2[] = {/* ??, ?? */ 0x9F, 0xE5, 0xFF, 0xFF, 0xFF, 0xEA, 0xC0, 0x00, 0x0C, 0xF1 };
    ptr = buggy_memmem(kdata, ksize, search2, sizeof(search2));
    if (ptr) {
      return ((uintptr_t)ptr) - 2 - ((uintptr_t)kdata);
    }

    printf("ERROR: Failed to locate larm_init_tramp.\n");
    exit(1);
}

static task_t get_kernel_task() {
    task_t kernel_task;
    if (KERN_SUCCESS != task_for_pid(mach_task_self(), 0, &kernel_task)) {
        printf("ERROR: task_for_pid 0 failed.\n");
        exit(1);
    }
    return kernel_task;
}

static vm_address_t get_kernel_base(task_t kernel_task) {
    vm_region_submap_info_data_64_t info;
    vm_size_t size;
    mach_msg_type_number_t info_count = VM_REGION_SUBMAP_INFO_COUNT_64;
    unsigned int depth = 0;
    vm_address_t addr = 0x81200000; /* arm64: addr = 0xffffff8000000000 */

    while (1) {
        if (KERN_SUCCESS != vm_region_recurse_64(kernel_task, &addr, &size, &depth, (vm_region_info_t) & info, &info_count))
            break;
        if (size > 1024 * 1024 * 1024) {
            /*
             * https://code.google.com/p/iphone-dataprotection/
             * hax, sometimes on iOS7 kernel starts at +0x200000 in the 1Gb region
             */
            pointer_t buf;
            mach_msg_type_number_t sz = 0;
            addr += 0x200000;
            vm_read(kernel_task, addr + 0x1000, 512, &buf, &sz);
            if (*((uint32_t *)buf) != MH_MAGIC) {
                addr -= 0x200000;
                vm_read(kernel_task, addr + 0x1000, 512, &buf, &sz);
                if (*((uint32_t*)buf) != MH_MAGIC) {
                    break;
                }
            }
            printf("kernel_base: 0x%08x\n", addr);
            return addr;
        }
        addr += size;
    }

    printf("ERROR: Failed to find kernel base.\n");
    exit(1);
}

static int get_cpid() {
    size_t size;
    sysctlbyname("kern.version", NULL, &size, NULL, 0);
    char *kern_version = malloc(size);
    if (sysctlbyname("kern.version", kern_version, &size, NULL, 0) == -1) {
        printf("ERROR: Failed to get kern.version sysctl.\n");
        exit(1);
    }
    printf("kern.version: %s\n", kern_version);

    uint32_t cpid = -1;
    if (strcasestr(kern_version, "s5l8920x")) {
        cpid = 0x8920;
    } else if (strcasestr(kern_version, "s5l8922x")) {
        cpid = 0x8922;
    } else if (strcasestr(kern_version, "s5l8930x")) {
        cpid = 0x8930;
    } else if (strcasestr(kern_version, "s5l8940x")) {
        cpid = 0x8940;
    } else if (strcasestr(kern_version, "s5l8942x")) {
        cpid = 0x8942;
    } else if (strcasestr(kern_version, "s5l8945x")) {
        cpid = 0x8945;
    } else if (strcasestr(kern_version, "s5l8947x")) {
        cpid = 0x8947;
    } else if (strcasestr(kern_version, "s5l8950x")) {
        cpid = 0x8950;
    } else if (strcasestr(kern_version, "s5l8955x")) {
        cpid = 0x8955;
    } else {
        printf("ERROR: Failed to recognize chip from kern.version.\n");
        exit(1);
    }

    free(kern_version);
    return cpid;
}

static void generate_ttb_entries(uint32_t gPhysBase, uint32_t phys_addr_remap, uint32_t ttb_remap_addr_base) {
    for (uint32_t i = SHADOWMAP_BEGIN, paddr = gPhysBase; i <= SHADOWMAP_END; i += SHADOWMAP_GRANULARITY, paddr += SHADOWMAP_GRANULARITY) {
        //printf("ProtoTTE: 0x%08x for VA 0x%08x -> PA 0x%08x\n", L1_PROTO_TTE(paddr), i, paddr);
        ttb_template[TTB_OFFSET(i) >> PFN_SHIFT] = L1_PROTO_TTE(paddr);
    }
    ttb_template[TTB_OFFSET(ttb_remap_addr_base) >> PFN_SHIFT] = L1_PROTO_TTE(phys_addr_remap);

    //printf("remap -> 0x%08x => 0x%08x (TTE: 0x%08x)\n", ttb_remap_addr_base, phys_addr_remap, L1_PROTO_TTE(phys_addr_remap));
    //printf("TTE offset begin for shadowmap: 0x%08x\n", SHADOWMAP_BEGIN_OFF);
    //printf("TTE offset end for shadowmap:   0x%08x\n", SHADOWMAP_END_OFF);
    //printf("TTE size:                       0x%08x\n", SHADOWMAP_SIZE);
    printf("New TTEs generated. Base address for remap: 0x%08x\n", phys_addr_remap);
}

static void dump_kernel(task_t kernel_task, vm_address_t kernel_base, uint8_t *dest) {
    for (vm_address_t addr = kernel_base + 0x1000, e = 0; addr < kernel_base + KERNEL_DUMP_SIZE; addr += CHUNK_SIZE, e += CHUNK_SIZE) {
        pointer_t buf = 0;
        vm_address_t sz = 0;
        vm_read(kernel_task, addr, CHUNK_SIZE, &buf, &sz);
        if (buf == 0 || sz == 0)
            continue;
        bcopy((uint8_t *)buf, dest + e, CHUNK_SIZE);
    }
}

static void write_tte_entries(task_t kernel_task, vm_address_t kernel_base, uint32_t gPhysBase, uint8_t *kernel_dump) {
    uint32_t kernel_pmap_offset = find_pmap_location(kernel_dump, KERNEL_DUMP_SIZE);
    if (0 == kernel_pmap_offset && kernel_base == DEFAULT_KERNEL_SLIDE) {
        /* find_pmap_location is only for iOS 6.0 and above, hopefully the second technique will work */
        kernel_pmap_offset = find_pmap_location_pre_iOS_6(kernel_base, kernel_dump, KERNEL_DUMP_SIZE);
    }
    if (0 == kernel_pmap_offset) {
        printf("ERROR: Failed to find kernel_pmap offset.");
        exit(1);
    }

    uint32_t kernel_pmap = kernel_base + 0x1000 + kernel_pmap_offset;
    printf("kernel_pmap: 0x%08x\n", kernel_pmap);
    pointer_t buf = 0;
    vm_address_t sz = 0;
    vm_read(kernel_task, kernel_pmap, 2048, &buf, &sz);
    vm_read(kernel_task, *(vm_address_t *)(buf), 2048, &buf, &sz);

    /* Copy it out to get the TTE base (we don't need to do this as TTEs should just remain constant after ToKD) */
    pmap_partial_t *part = (pmap_partial_t *) buf;
    printf("kernel_pmap->tte_virt: 0x%08x\n", part->tte_virt);
    printf("kernel_pmap->tte_phys: 0x%08x\n", part->tte_phys);
    printf("gPhysBase: 0x%08x\n", gPhysBase);
    if (gPhysBase != (part->tte_phys & ~0xFFFFFFF)) {
        printf("ERROR: Unexpected value for gPhysBase, should be: 0x%08x\n", part->tte_phys & ~0xFFFFFFF);
        exit(1);
    }

    /* Now, we can start reading at the TTE base and start writing in the descriptors */
    vm_read(kernel_task, SHADOWMAP_BEGIN_OFF + part->tte_virt, 2048, &buf, &sz);
    bcopy(SHADOWMAP_BEGIN_OFF + (uint8_t *)ttb_template, (void *)buf, SHADOWMAP_SIZE);
    vm_write(kernel_task, SHADOWMAP_BEGIN_OFF + part->tte_virt, buf, sz);

    printf("======================================================================================\n");
    printf("!!!! Kernel TTE entries written. System stability is no longer guaranteed.            \n");
    printf("!!!! Security has also been reduced by an exponential factor. You have been warned.   \n");
    printf("======================================================================================\n");
}

static void load_image_to_memory(const char *filename, uint8_t *addr) {
    FILE *f = fopen(filename, "rb");
    if (!f) {
        printf("ERROR: Failed to open the image file.\n");
        exit(1);
    }

    fseek(f, 0, SEEK_END);
    int length = ftell(f);
    fseek(f, 0, SEEK_SET);

    uint8_t *image = malloc(length);
    if (!image) {
        printf("ERROR: Failed to allocate memory for image.\n");
        exit(1);
    }

    fread(image, length, 1, f);
    fclose(f);
    printf("Read image into buffer: %p length: %d\n", image, length);
    if (*(uint32_t *)image == 'Img3') {
        printf("ERROR: This is an IMG3 file. For now, only unpacked raw images are supported. IMG3 support is coming soon.\n");
        exit(1);
    }
    bcopy(image, addr, length);
    free(image);

    /* Verify ARM header */
    if (*(uint32_t *)addr != 0xea00000e) {
        printf("This doesn't seem like an ARM image, perhaps it failed to copy? Continuing though.\n");
    }

    printf("Image information: %s\n", addr + 0x200);
    printf("Image information: %s\n", addr + 0x240);
    printf("Image information: %s\n", addr + 0x280);
}

static void schedule_autowake_during_sleep_notification(CFTimeInterval autowake_delay) {
    int out_token;
    uint32_t status = notify_register_dispatch(kIOPMSystemPowerStateNotify, &out_token, dispatch_get_main_queue(), ^(int token) {
        CFDateRef date = CFDateCreate(0, CFAbsoluteTimeGetCurrent() + autowake_delay);
        kern_return_t kr = IOPMSchedulePowerEvent(date, NULL, CFSTR(kIOPMSettingDebugWakeRelativeKey));
        if (kr) {
            printf("ERROR: IOPMSchedulePowerEvent returned %x.\n", kr);
            exit(1);
        }
        printf("Device should wake up in %.1f seconds.\n", autowake_delay);

        /* Stop the runloop */
        CFRunLoopStop(CFRunLoopGetCurrent());
    });

    if (NOTIFY_STATUS_OK != status) {
        printf("ERROR: Failed to register for kIOPMSystemPowerStateNotify: %x\n", status);
        exit(1);
    }
}

static void hook_kernel_wakeup(uint8_t *kernel_dump, uint32_t phys_addr_remap) {
    uint32_t arm[2] = { 0xe51ff004, phys_addr_remap };
    /* Requires D-cache writeback */
    uint32_t larm_init_tramp = 0x1000 + find_larm_init_tramp(kernel_dump, KERNEL_DUMP_SIZE) + SHADOWMAP_BEGIN;
    printf("Tramp %x COMMMAP\n", larm_init_tramp);
    printf("%lx, %lx\n", *(uintptr_t *) (larm_init_tramp), *(uintptr_t *) (larm_init_tramp + 4));
    printf("%x\n", *(uint32_t *) (0x7f000000 + 0x1000));
    bcopy((void *) arm, (void *) larm_init_tramp, sizeof(arm));
    printf("%lx, %lx\n", *(uintptr_t *) (larm_init_tramp), *(uintptr_t *) (larm_init_tramp + 4));
    printf("%x\n", *(uint32_t *) (0x7f000000 + 0x1000));
}

static void request_sleep() {
    printf("Syncing disks.\n");
    for (int disk_sync = 0; disk_sync < 10; disk_sync++) {
        sync();
    }

    mach_port_t fb = IOPMFindPowerManagement(MACH_PORT_NULL);
    if (fb == MACH_PORT_NULL) {
        printf("ERROR: Failed to get PowerManagement root port.\n");
        exit(1);
    }

    printf("Magic happening now. (Attempted!)\n");
    for (int i = 0; i < 10; i++) {
        kern_return_t kr = IOPMSleepSystem(fb);
        if (!kr) {
            return;
        }
        printf("WARNING: IOPMSleepSystem returned %x. Trying again.\n", kr);
        sleep(1);
    }
    printf("ERROR: IOPMSleepSystem failed.\n");
    exit(1);
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        printf("usage: %s [loadfile]\n", argv[0]);
        printf("This will destroy the current running OS instance and fire up the loaded image.\n");
        printf("You have been warned.\n");
        exit(1);
    }

    uint32_t gPhysBase = 0xdeadbeef;
    uint32_t phys_addr_remap = 0xdeadbeef;
    switch (get_cpid()) {
        case 0x8920:
        case 0x8922:
            gPhysBase = 0x40000000;
            phys_addr_remap = 0x4fe00000;
            break;

        case 0x8930:
            gPhysBase = 0x40000000;
            phys_addr_remap = 0x5fe00000;
            break;

        case 0x8940:
        case 0x8942:
        case 0x8947:
            gPhysBase = 0x80000000;
            phys_addr_remap = 0x9fe00000;
            break;

        case 0x8945:
        case 0x8950:
        case 0x8955:
            gPhysBase = 0x80000000;
            phys_addr_remap = 0xbfe00000;
            break;

        default:
            printf("ERROR: Failed to recognize the chip.\n");
            exit(1);
    }

    task_t kernel_task = get_kernel_task();
    vm_address_t kernel_base = get_kernel_base(kernel_task);
    dump_kernel(kernel_task, kernel_base, kernel_dump);
    signal(SIGINT, SIG_IGN);

    /* Remap TTE for iBoot load address */
    uint32_t ttb_remap_addr_base = 0x7fe00000;
    generate_ttb_entries(gPhysBase, phys_addr_remap, ttb_remap_addr_base);
    write_tte_entries(kernel_task, kernel_base, gPhysBase, kernel_dump);
    load_image_to_memory(argv[1], (uint8_t *)ttb_remap_addr_base);
    hook_kernel_wakeup(kernel_dump, phys_addr_remap);
    schedule_autowake_during_sleep_notification(2.0);
    request_sleep();
    CFRunLoopRun();

    return 0;
}
