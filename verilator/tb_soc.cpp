// ============================================================================
// Verilator Testbench for Sparkle RV32I SoC
//
// Loads firmware hex file, runs simulation, monitors UART output.
// Usage: ./Vrv32i_soc [firmware.hex] [max_cycles] [--dram <binary>] [--dtb <dtb_file>] [--payload <binary>]
// ============================================================================

#include "Vrv32i_soc.h"
#include "Vrv32i_soc___024root.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>

// Load hex file (one 32-bit word per line, hex format)
static std::vector<uint32_t> load_hex(const std::string& path) {
    std::vector<uint32_t> words;
    std::ifstream f(path);
    if (!f.is_open()) {
        fprintf(stderr, "Error: cannot open %s\n", path.c_str());
        return words;
    }
    std::string line;
    while (std::getline(f, line)) {
        if (line.empty() || line[0] == '/' || line[0] == '#' || line[0] == '@') continue;
        uint32_t val = (uint32_t)strtoul(line.c_str(), nullptr, 16);
        words.push_back(val);
    }
    return words;
}

// Load raw binary file into byte vector
static std::vector<uint8_t> load_binary(const std::string& path) {
    std::vector<uint8_t> data;
    std::ifstream f(path, std::ios::binary);
    if (!f.is_open()) {
        fprintf(stderr, "Error: cannot open binary %s\n", path.c_str());
        return data;
    }
    f.seekg(0, std::ios::end);
    size_t sz = f.tellg();
    f.seekg(0, std::ios::beg);
    data.resize(sz);
    f.read(reinterpret_cast<char*>(data.data()), sz);
    return data;
}

// Load binary data into DMEM via write port during reset
// base_addr is the physical byte address (e.g. 0x80000000)
static void load_dram(Vrv32i_soc* dut, VerilatedVcdC* vcd,
                      const uint8_t* data, size_t len,
                      uint32_t base_addr, uint64_t& time_ps) {
    // Convert base_addr to word address: addr[24:2]
    // Physical address 0x80000000 maps to DMEM word address 0
    uint32_t word_addr_base = (base_addr & 0x01FFFFFF) >> 2;
    size_t num_words = (len + 3) / 4;

    printf("Loading %zu bytes (%zu words) to DRAM at 0x%08x (word addr 0x%06x)\n",
           len, num_words, base_addr, word_addr_base);

    for (size_t i = 0; i < num_words; i++) {
        uint32_t word = 0;
        for (int b = 0; b < 4; b++) {
            size_t idx = i * 4 + b;
            if (idx < len) word |= ((uint32_t)data[idx]) << (b * 8);
        }
        dut->dmem_wr_en = 1;
        dut->dmem_wr_addr = word_addr_base + i;
        dut->dmem_wr_data = word;

        dut->clk = 0; dut->eval();
        if (vcd) vcd->dump(time_ps++);
        dut->clk = 1; dut->eval();
        if (vcd) vcd->dump(time_ps++);
    }
    dut->dmem_wr_en = 0;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    std::string hex_path = "../firmware/firmware.hex";
    uint64_t max_cycles = 100000;
    std::string dram_path;
    std::string dtb_path;
    std::string payload_path;

    // Parse arguments: positional: <hex_path> [max_cycles], named: --dram/--dtb/--payload
    int pos_idx = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--dram") == 0 && i + 1 < argc) {
            dram_path = argv[++i];
        } else if (strcmp(argv[i], "--dtb") == 0 && i + 1 < argc) {
            dtb_path = argv[++i];
        } else if (strcmp(argv[i], "--payload") == 0 && i + 1 < argc) {
            payload_path = argv[++i];
        } else if (argv[i][0] != '-') {
            if (pos_idx == 0) { hex_path = argv[i]; pos_idx++; }
            else if (pos_idx == 1) { max_cycles = strtoull(argv[i], nullptr, 10); pos_idx++; }
        }
    }

    // Load firmware
    auto firmware = load_hex(hex_path);
    printf("Loading firmware from %s...\n", hex_path.c_str());
    printf("Loaded %zu words\n", firmware.size());

    // Instantiate DUT
    Vrv32i_soc* dut = new Vrv32i_soc;

    // VCD tracing (disabled for performance — enable for waveform debug)
    VerilatedVcdC* vcd = nullptr;
    // Verilated::traceEverOn(true);
    // vcd = new VerilatedVcdC;
    // dut->trace(vcd, 99);
    // vcd->open("sim_trace.vcd");

    // Initialize firmware into IMEM via backdoor
    // Write firmware words during reset
    dut->clk = 0;
    dut->rst = 1;
    dut->imem_wr_en = 0;
    dut->imem_wr_addr = 0;
    dut->imem_wr_data = 0;
    dut->dmem_wr_en = 0;
    dut->dmem_wr_addr = 0;
    dut->dmem_wr_data = 0;
    dut->uart_rx_valid = 0;
    dut->uart_rx_data = 0;
    dut->eval();

    // Load firmware via IMEM write port during reset
    uint64_t time_ps = 0;
    for (size_t i = 0; i < firmware.size() && i < (1 << 12); i++) {
        dut->imem_wr_en = 1;
        dut->imem_wr_addr = (uint16_t)i;
        dut->imem_wr_data = firmware[i];
        dut->clk = 0; dut->eval();
        if (vcd) vcd->dump(time_ps++);
        dut->clk = 1; dut->eval();
        if (vcd) vcd->dump(time_ps++);
    }
    dut->imem_wr_en = 0;

    // Load DRAM binary (e.g. OpenSBI fw_jump.bin) at 0x80000000
    if (!dram_path.empty()) {
        auto dram_data = load_binary(dram_path);
        if (!dram_data.empty()) {
            load_dram(dut, vcd, dram_data.data(), dram_data.size(),
                      0x80000000, time_ps);
        }
    }

    // Load DTB at 0x80F00000
    if (!dtb_path.empty()) {
        auto dtb_data = load_binary(dtb_path);
        if (!dtb_data.empty()) {
            load_dram(dut, vcd, dtb_data.data(), dtb_data.size(),
                      0x80F00000, time_ps);
        }
    }

    // Check DTB integrity BEFORE kernel loading
    if (!dtb_path.empty()) {
        auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
        auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
        auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
        auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
        uint32_t w8D = b0[0x3C008D] | (b1[0x3C008D] << 8) | (b2[0x3C008D] << 16) | (b3[0x3C008D] << 24);
        printf("PRE-KERNEL-LOAD: DTB[0x8D]=0x%08x (expected 0x03000000)\n", w8D);
    }

    // Load payload (e.g. Linux kernel) at 0x80400000 (FW_JUMP_ADDR, 4MB-aligned for Sv32 megapages)
    if (!payload_path.empty()) {
        auto payload_data = load_binary(payload_path);
        if (!payload_data.empty()) {
            load_dram(dut, vcd, payload_data.data(), payload_data.size(),
                      0x80400000, time_ps);
        }
    }

    // Check DTB integrity AFTER kernel loading
    if (!dtb_path.empty()) {
        auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
        auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
        auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
        auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
        uint32_t w8D = b0[0x3C008D] | (b1[0x3C008D] << 8) | (b2[0x3C008D] << 16) | (b3[0x3C008D] << 24);
        printf("POST-KERNEL-LOAD: DTB[0x8D]=0x%08x (expected 0x03000000)\n", w8D);
    }

    // === Verify DTB content in DMEM right after loading ===
    if (!dtb_path.empty()) {
        auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
        auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
        auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
        auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
        printf("=== DTB verification after loading ===\n");
        printf("DTB loaded at word addr 0x3C0000 (PA 0x80F00000)\n");
        // Dump first 16 words of the DTB from DMEM byte lanes
        for (int w = 0; w < 16; w++) {
            uint32_t a = 0x3C0000 + w;
            uint8_t byte0 = b0[a], byte1 = b1[a], byte2 = b2[a], byte3 = b3[a];
            uint32_t word_le = byte0 | (byte1 << 8) | (byte2 << 16) | (byte3 << 24);
            uint32_t word_be = byte3 | (byte2 << 8) | (byte1 << 16) | (byte0 << 24);
            printf("  DTB[%2d] @ word 0x%06x: bytes=[%02x %02x %02x %02x] LE=0x%08x BE=0x%08x\n",
                   w, a, byte0, byte1, byte2, byte3, word_le, word_be);
        }
        // Also verify FDT magic: first 4 bytes should be D0 0D FE ED
        uint8_t m0 = b0[0x3C0000], m1 = b1[0x3C0000], m2 = b2[0x3C0000], m3 = b3[0x3C0000];
        uint32_t magic_be = (m0 << 24) | (m1 << 16) | (m2 << 8) | m3;
        printf("FDT magic (big-endian reconstruct): 0x%08x %s\n",
               magic_be, magic_be == 0xD00DFEED ? "CORRECT" : "*** WRONG ***");
        // Extended DTB verification: check key addresses (reg property at word 0x3C008D)
        printf("DTB extended verification:\n");
        auto dtb_verify2 = load_binary(dtb_path);
        int mismatches = 0;
        for (size_t i = 0; i < dtb_verify2.size() && i < 1108; i += 4) {
            uint32_t w = 0x3C0000 + i / 4;
            uint32_t expected = 0;
            for (int b = 0; b < 4 && (i+b) < dtb_verify2.size(); b++)
                expected |= ((uint32_t)dtb_verify2[i+b]) << (b * 8);
            uint32_t actual = b0[w] | (b1[w] << 8) | (b2[w] << 16) | (b3[w] << 24);
            if (w == 0x3C008D) {
                printf("  VERIFY DEBUG: w=0x%06x i=%zu expected=0x%08x actual=0x%08x bytes=[%02x %02x %02x %02x]\n",
                       w, i, expected, actual, (uint8_t)b0[w], (uint8_t)b1[w], (uint8_t)b2[w], (uint8_t)b3[w]);
            }
            if (actual != expected) {
                mismatches++;
                if (mismatches <= 10)
                    printf("  MISMATCH word 0x%06x: expected=0x%08x actual=0x%08x (DTB byte 0x%zx)\n",
                           w, expected, actual, i);
            }
        }
        if (mismatches == 0) printf("  ALL %zu DTB words VERIFIED OK\n", dtb_verify2.size() / 4);
        else printf("  *** %d MISMATCHES out of %zu words ***\n", mismatches, dtb_verify2.size() / 4);
        // Read the DTB file directly for comparison
        auto dtb_verify = load_binary(dtb_path);
        if (dtb_verify.size() >= 16) {
            printf("DTB file first 16 bytes: ");
            for (int i = 0; i < 16; i++) printf("%02x ", dtb_verify[i]);
            printf("\n");
            // Compare first 64 bytes of DTB file vs DMEM content
            bool mismatch = false;
            for (size_t i = 0; i < std::min(dtb_verify.size(), (size_t)64); i++) {
                uint32_t word_idx = 0x3C0000 + i / 4;
                uint8_t dmem_byte;
                switch (i % 4) {
                    case 0: dmem_byte = b0[word_idx]; break;
                    case 1: dmem_byte = b1[word_idx]; break;
                    case 2: dmem_byte = b2[word_idx]; break;
                    case 3: dmem_byte = b3[word_idx]; break;
                }
                if (dmem_byte != dtb_verify[i]) {
                    printf("  MISMATCH at byte %zu: DMEM=0x%02x, file=0x%02x\n",
                           i, dmem_byte, dtb_verify[i]);
                    mismatch = true;
                }
            }
            if (!mismatch) printf("DTB first 64 bytes: VERIFIED OK\n");
        }
        printf("=== End DTB verification ===\n");
    }

    // Release reset
    dut->rst = 0;

    // Simulation
    printf("Running Verilator simulation for %llu cycles...\n",
           (unsigned long long)max_cycles);

    // Determine mode: OpenSBI (has DRAM) vs firmware test
    bool opensbi_mode = !dram_path.empty();

    uint32_t prev_pc = 0xFFFFFFFF;
    int halt_count = 0;
    std::vector<uint32_t> uart_log;

    for (uint64_t cycle = 0; cycle < max_cycles; cycle++) {
        // === BEFORE rising edge: sample write signals (these feed the BRAM write on posedge) ===
        uint32_t mon_wr_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_dmem_write_addr;
        uint8_t mon_wr_en = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte0_we;
        uint32_t mon_old_val = 0;
        bool mon_match = mon_wr_en && (mon_wr_addr == 0x17DF00 || mon_wr_addr == 0x155F00 ||
                          mon_wr_addr == 0x156152 || mon_wr_addr == 0x156153 ||  // dt_root_size/addr_cells
                          (mon_wr_addr >= 0x156155 && mon_wr_addr <= 0x156180) ||  // memblock struct + init_regions
                          (mon_wr_addr >= 0x17D000 && mon_wr_addr <= 0x17E000) ||
                          (mon_wr_addr >= 0x155C00 && mon_wr_addr <= 0x156000) ||
                          (mon_wr_addr >= 0x15F946 && mon_wr_addr <= 0x15F94C) ||  // kernel_map struct
                          (mon_wr_addr >= 0x3C0000 && mon_wr_addr <= 0x3C0120));  // DTB area (entire struct block)
        if (mon_match) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            mon_old_val = b0[mon_wr_addr] | (b1[mon_wr_addr] << 8) |
                          (b2[mon_wr_addr] << 16) | (b3[mon_wr_addr] << 24);
        }

        // Rising edge
        dut->clk = 1;
        dut->eval();
        time_ps++;
        if (vcd) vcd->dump(time_ps);

        // Sample outputs on rising edge
        uint32_t pc = dut->pc_out;
        bool uart_valid = dut->uart_tx_valid;
        uint32_t uart_data = dut->uart_tx_data;

        // Debug: satp + PTW state
        uint32_t satp_reg = dut->mepc_debug;         // satpReg via wrapper
        uint32_t ptw_pte = dut->idex_pc_debug;       // ptwPteReg via wrapper
        uint32_t ptw_vaddr = dut->trap_cause_out;    // ptwVaddrReg via wrapper

        // Print PC for first few cycles, periodically, and at region transitions
        static uint32_t prev_pc_log = 0;
        bool pc_changed_region = ((pc & 0xF0000000) != (prev_pc_log & 0xF0000000));
        if (cycle < 5 || cycle % 100000 == 0 || pc_changed_region) {
            printf("cycle %llu: PC = 0x%08x satp=0x%08x ptwPte=0x%08x ptwVaddr=0x%08x\n",
                   (unsigned long long)cycle, pc, satp_reg, ptw_pte, ptw_vaddr);
        }

        prev_pc_log = pc;

        // === Trap debug logging ===
#ifdef TRACE_INTERNAL_SIGNALS
        {
            uint8_t trap_taken_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_trap_taken;
            if (trap_taken_sig) {
                uint32_t trap_cause_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_trapCause;
                printf("*** TRAP at cycle %llu: PC=0x%08x cause=0x%08x",
                       (unsigned long long)cycle, pc, trap_cause_sig);
                if (trap_cause_sig == 0x00000002) printf(" (illegal instruction)");
                else if (trap_cause_sig == 0x00000008) printf(" (U-mode ecall)");
                else if (trap_cause_sig == 0x00000009) printf(" (S-mode ecall)");
                else if (trap_cause_sig == 0x0000000B) printf(" (M-mode ecall)");
                else if (trap_cause_sig == 0x0000000C) printf(" (instruction page fault)");
                else if (trap_cause_sig == 0x0000000D) printf(" (load page fault)");
                else if (trap_cause_sig == 0x0000000F) printf(" (store page fault)");
                else if (trap_cause_sig == 0x80000003) printf(" (SW interrupt)");
                else if (trap_cause_sig == 0x80000007) printf(" (timer interrupt)");
                printf("\n");
            }
        }
#endif

        // === AFTER rising edge: log DMEM write using pre-edge sampled values ===
        if (mon_match) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t new_val = b0[mon_wr_addr] | (b1[mon_wr_addr] << 8) |
                               (b2[mon_wr_addr] << 16) | (b3[mon_wr_addr] << 24);
            // Only log non-zero writes or writes that change the value
            if (new_val != 0 || mon_old_val != 0) {
                printf("cycle %llu: DMEM-WR @ 0x%06x  old=0x%08x -> new=0x%08x  PC=0x%08x\n",
                       (unsigned long long)cycle, mon_wr_addr, mon_old_val, new_val, pc);
            }
            // Extra detail for kernel_map writes: show byte enables and wdata
            if (mon_wr_addr >= 0x15F946 && mon_wr_addr <= 0x15F94C) {
                uint8_t we0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte0_we;
                uint8_t we1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte1_we;
                uint8_t we2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte2_we;
                uint8_t we3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte3_we;
                printf("  byte enables: b0=%d b1=%d b2=%d b3=%d\n", we0, we1, we2, we3);
            }
        }
        // === Periodic DTB integrity check ===
        {
            static bool dtb_corrupted = false;
            if (!dtb_corrupted && cycle % 1000 == 0) {
                auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
                auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
                auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
                auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
                // Check DTB word 0x3C008E (DTB offset 0x238): expected 0x00007972
                uint32_t val = b0[0x3C008E] | (b1[0x3C008E] << 8) | (b2[0x3C008E] << 16) | (b3[0x3C008E] << 24);
                if (val != 0x00007972) {
                    printf("*** DTB CORRUPTION DETECTED at cycle %llu: DTB[0x8E]=0x%08x (expected 0x00007972) PC=0x%08x ***\n",
                           (unsigned long long)cycle, val, pc);
                    // Also check a few nearby words
                    uint32_t v8d = b0[0x3C008D] | (b1[0x3C008D] << 8) | (b2[0x3C008D] << 16) | (b3[0x3C008D] << 24);
                    uint32_t v8f = b0[0x3C008F] | (b1[0x3C008F] << 8) | (b2[0x3C008F] << 16) | (b3[0x3C008F] << 24);
                    uint32_t v90 = b0[0x3C0090] | (b1[0x3C0090] << 8) | (b2[0x3C0090] << 16) | (b3[0x3C0090] << 24);
                    printf("  Context: DTB[0x8D]=0x%08x [0x8F]=0x%08x [0x90]=0x%08x\n", v8d, v8f, v90);
                    dtb_corrupted = true;
                }
            }
        }
        // === Monitor memblock functions (exact PC checks) ===
        if (pc == 0xC0153F8C) {
            printf("cycle %llu: ENTERED memblock_add (IF stage)\n", (unsigned long long)cycle);
        }
        if (pc == 0xC0153D40) {
            printf("cycle %llu: ENTERED memblock_add_range (IF stage)\n", (unsigned long long)cycle);
        }
        // Monitor early_init_dt_add_memory_arch entry and key branch points
        if (pc == 0xC0151238) {
            printf("cycle %llu: ENTERED early_init_dt_add_memory_arch (IF stage)\n", (unsigned long long)cycle);
        }
        // C015128C: normal path (no overflow)
        if (pc == 0xC015128C) {
            printf("cycle %llu: early_init_dt_add_memory_arch NORMAL PATH (C015128C)\n", (unsigned long long)cycle);
        }
        // C01512A4: register restore → leads to _printk (ERROR/WARNING path)
        if (pc == 0xC01512A4) {
            printf("cycle %llu: early_init_dt_add_memory_arch RESTORE→PRINTK path (C01512A4)\n", (unsigned long long)cycle);
        }
        // C01512C0: j _printk — returns WITHOUT calling memblock_add
        if (pc == 0xC01512C0) {
            printf("cycle %llu: early_init_dt_add_memory_arch JUMP TO PRINTK (C01512C0) — NO memblock_add!\n", (unsigned long long)cycle);
        }
        // C01512C4: clamping path
        if (pc == 0xC01512C4) {
            printf("cycle %llu: early_init_dt_add_memory_arch CLAMP PATH (C01512C4)\n", (unsigned long long)cycle);
        }
        // C0151350: final check before memblock_add
        if (pc == 0xC0151350) {
            printf("cycle %llu: early_init_dt_add_memory_arch FINAL CHECK (C0151350)\n", (unsigned long long)cycle);
        }
        // C0151384: restore regs before tail call
        if (pc == 0xC0151384) {
            printf("cycle %llu: early_init_dt_add_memory_arch PRE-TAILCALL (C0151384)\n", (unsigned long long)cycle);
        }
        // C015139C: j memblock_add — SUCCESS path
        if (pc == 0xC015139C) {
            printf("cycle %llu: early_init_dt_add_memory_arch TAIL-CALL memblock_add (C015139C) — SUCCESS\n", (unsigned long long)cycle);
        }
        // Monitor the simple-case store instructions in memblock_add_range
        if (pc == 0xC0153D9C || pc == 0xC0153DA4 || pc == 0xC0153DAC || pc == 0xC0153DB0) {
            printf("cycle %llu: memblock_add_range STORE instruction in IF stage, PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        // === Trace around EACH memblock_add_range entry (up to 4 calls) ===
        static uint64_t mbar_entry_cycles[4] = {0};
        static int mbar_call_count = 0;
        if (pc == 0xC0153D40) {
            if (mbar_call_count < 4) {
                mbar_entry_cycles[mbar_call_count] = cycle;
                printf("  === memblock_add_range call #%d at cycle %llu ===\n",
                       mbar_call_count, (unsigned long long)cycle);
                // Dump memblock DMEM values at entry
                auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
                auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
                auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
                auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
                // memblock.memory: cnt(0x156157), max(0x156158), total_size(0x156159), regions_ptr(0x15615A)
                uint32_t mem_cnt  = b0[0x156157] | (b1[0x156157]<<8) | (b2[0x156157]<<16) | (b3[0x156157]<<24);
                uint32_t mem_max  = b0[0x156158] | (b1[0x156158]<<8) | (b2[0x156158]<<16) | (b3[0x156158]<<24);
                uint32_t mem_ts   = b0[0x156159] | (b1[0x156159]<<8) | (b2[0x156159]<<16) | (b3[0x156159]<<24);
                uint32_t mem_rptr = b0[0x15615A] | (b1[0x15615A]<<8) | (b2[0x15615A]<<16) | (b3[0x15615A]<<24);
                printf("    memory: cnt=%u max=%u total_size=0x%08x regions_ptr=0x%08x\n",
                       mem_cnt, mem_max, mem_ts, mem_rptr);
                // memory regions[0]: base(0x156166), size(0x156167), flags(0x156168)
                uint32_t mr_base  = b0[0x156166] | (b1[0x156166]<<8) | (b2[0x156166]<<16) | (b3[0x156166]<<24);
                uint32_t mr_size  = b0[0x156167] | (b1[0x156167]<<8) | (b2[0x156167]<<16) | (b3[0x156167]<<24);
                uint32_t mr_flags = b0[0x156168] | (b1[0x156168]<<8) | (b2[0x156168]<<16) | (b3[0x156168]<<24);
                printf("    memory.regions[0]: base=0x%08x size=0x%08x flags=0x%08x\n",
                       mr_base, mr_size, mr_flags);
                // reserved: cnt, total_size, regions_ptr
                uint32_t res_cnt  = b0[0x15615C] | (b1[0x15615C]<<8) | (b2[0x15615C]<<16) | (b3[0x15615C]<<24);
                uint32_t res_ts   = b0[0x15615E] | (b1[0x15615E]<<8) | (b2[0x15615E]<<16) | (b3[0x15615E]<<24);
                uint32_t res_rptr = b0[0x15615F] | (b1[0x15615F]<<8) | (b2[0x15615F]<<16) | (b3[0x15615F]<<24);
                printf("    reserved: cnt=%u total_size=0x%08x regions_ptr=0x%08x\n",
                       res_cnt, res_ts, res_rptr);
                // reserved regions[0]: base(0x1562E6), size(0x1562E7), flags(0x1562E8)
                uint32_t rr_base  = b0[0x1562E6] | (b1[0x1562E6]<<8) | (b2[0x1562E6]<<16) | (b3[0x1562E6]<<24);
                uint32_t rr_size  = b0[0x1562E7] | (b1[0x1562E7]<<8) | (b2[0x1562E7]<<16) | (b3[0x1562E7]<<24);
                uint32_t rr_flags = b0[0x1562E8] | (b1[0x1562E8]<<8) | (b2[0x1562E8]<<16) | (b3[0x1562E8]<<24);
                printf("    reserved.regions[0]: base=0x%08x size=0x%08x flags=0x%08x\n",
                       rr_base, rr_size, rr_flags);
                mbar_call_count++;
            }
        }
        // Print detailed trace for 200 cycles after each memblock_add_range entry
        {
            bool in_trace = false;
            for (int i = 0; i < mbar_call_count; i++) {
                if (mbar_entry_cycles[i] > 0 && cycle >= mbar_entry_cycles[i] && cycle < mbar_entry_cycles[i] + 200) {
                    in_trace = true;
                    break;
                }
            }
            if (in_trace) {
#ifdef TRACE_INTERNAL_SIGNALS
                uint8_t sup_exwb = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_suppressEXWB != 0;
                uint8_t div_stall = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_divStall != 0;
                uint8_t dtlb_miss = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dTLBMiss;
                uint8_t stall_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_stall;
                uint32_t wr_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_dmem_write_addr;
                uint8_t wr_en0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte0_we;
                uint8_t flush_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_flush;
                uint32_t rd_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
                printf("  [MBAR] cy=%llu PC=0x%08x supEXWB=%d divStall=%d dMiss=%d stall=%d flush=%d wrEn=%d wrAddr=0x%06x rdAddr=0x%06x\n",
                       (unsigned long long)cycle, pc, sup_exwb, div_stall, dtlb_miss, stall_sig, flush_sig, wr_en0, wr_addr, rd_addr);
#else
                printf("  [MBAR] cy=%llu PC=0x%08x\n", (unsigned long long)cycle, pc);
#endif
            }
        }
        // early_init_dt_scan_memory EXACT entry (C01513A0)
        static uint64_t dt_scan_mem_entry = 0;
        if (pc == 0xC01513A0) {
            dt_scan_mem_entry = cycle;
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t ibp = b0[0x15F99E] | (b1[0x15F99E] << 8) |
                           (b2[0x15F99E] << 16) | (b3[0x15F99E] << 24);
            printf("cycle %llu: ENTERED early_init_dt_scan_memory (EXACT) initial_boot_params=0x%08x\n",
                   (unsigned long long)cycle, ibp);
            // Dump the modified DTB from DRAM to a file for analysis
            {
                static bool dtb_dumped = false;
                if (!dtb_dumped) {
                    dtb_dumped = true;
                    // Read totalsize from header (big-endian at DTB+4)
                    uint32_t ts_le = b0[0x3C0001] | (b1[0x3C0001] << 8) | (b2[0x3C0001] << 16) | (b3[0x3C0001] << 24);
                    uint32_t totalsize = ((ts_le & 0xFF) << 24) | (((ts_le >> 8) & 0xFF) << 16) |
                                         (((ts_le >> 16) & 0xFF) << 8) | ((ts_le >> 24) & 0xFF);
                    printf("  Dumping modified DTB: totalsize=%u (0x%x) bytes\n", totalsize, totalsize);
                    FILE* df = fopen("/tmp/modified_dtb.dtb", "wb");
                    if (df) {
                        size_t nwords = (totalsize + 3) / 4;
                        for (size_t w = 0; w < nwords; w++) {
                            uint32_t a = 0x3C0000 + w;
                            uint8_t bytes[4] = {
                                (uint8_t)b0[a], (uint8_t)b1[a],
                                (uint8_t)b2[a], (uint8_t)b3[a]
                            };
                            fwrite(bytes, 1, 4, df);
                        }
                        fclose(df);
                        printf("  DTB written to /tmp/modified_dtb.dtb\n");
                    }
                }
            }
        }
        // Trace PCs + DMEM reads for first 5500 cycles of early_init_dt_scan_memory
        if (dt_scan_mem_entry > 0 && cycle >= dt_scan_mem_entry && cycle < dt_scan_mem_entry + 5500) {
            static uint32_t last_scan_pc = 0;
            if (pc != last_scan_pc) {
                printf("  SCAN cycle %llu: PC=0x%08x\n", (unsigned long long)cycle, pc);
                last_scan_pc = pc;
            }
            // Trace DMEM read address to see if DTB area is being accessed
            uint32_t dmem_rd_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
            // DTB range: word addr 0x3C0000 - 0x3C1000 (16KB)
            if (dmem_rd_addr >= 0x3C0000 && dmem_rd_addr < 0x3C1000) {
                // Read the actual byte values from the memory arrays
                auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
                auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
                auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
                auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
                uint32_t word = b0[dmem_rd_addr] | (b1[dmem_rd_addr] << 8) |
                                (b2[dmem_rd_addr] << 16) | (b3[dmem_rd_addr] << 24);
                printf("  DTB-RD cycle %llu: dmem_read_addr=0x%06x word=0x%08x PC=0x%08x\n",
                       (unsigned long long)cycle, dmem_rd_addr, word, pc);
            }
        }
        // (Old DTB-SCAN trace replaced by REG-DTB comprehensive trace above)
        // of_scan_flat_dt entry (C0150738)
        if (pc == 0xC0150738) {
            printf("cycle %llu: ENTERED of_scan_flat_dt\n", (unsigned long long)cycle);
        }
        // early_init_dt_scan_root entry (C0150C0C)
        if (pc == 0xC0150C0C) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t ac = b0[0x156153] | (b1[0x156153] << 8) | (b2[0x156153] << 16) | (b3[0x156153] << 24);
            uint32_t sc = b0[0x156152] | (b1[0x156152] << 8) | (b2[0x156152] << 16) | (b3[0x156152] << 24);
            printf("cycle %llu: ENTERED early_init_dt_scan_root addr_cells=%u size_cells=%u\n",
                   (unsigned long long)cycle, ac, sc);
        }
        // Monitor sw instructions in early_init_dt_scan_root (store defaults + DTB values)
        // sw a5,0(s0) at C0150C54 → stores 1 to dt_root_size_cells
        // sw a5,4(s0) at C0150C58 → stores 1 to dt_root_addr_cells
        // sw a0,0(s0) at C0150C6C → stores be32-swapped #size-cells from DTB
        // sw a0,4(s0) at C0150C90 → stores be32-swapped #address-cells from DTB
        if (pc == 0xC0150C54 || pc == 0xC0150C58 || pc == 0xC0150C6C || pc == 0xC0150C90) {
            printf("cycle %llu: early_init_dt_scan_root: SW at PC=0x%08x (store to dt_root cells)\n",
                   (unsigned long long)cycle, pc);
        }
        // Also trace the beqz checks that skip the stores (of_get_flat_dt_prop returns NULL?)
        if (pc == 0xC0150C60 || pc == 0xC0150C84) {
            printf("cycle %llu: early_init_dt_scan_root: beqz at PC=0x%08x (skip if prop NULL)\n",
                   (unsigned long long)cycle, pc);
        }
        // Dump dt_root cells after early_init_dt_scan_root returns (ret at C0150CAC)
        if (pc == 0xC0150CAC) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t ac = b0[0x156153] | (b1[0x156153] << 8) | (b2[0x156153] << 16) | (b3[0x156153] << 24);
            uint32_t sc = b0[0x156152] | (b1[0x156152] << 8) | (b2[0x156152] << 16) | (b3[0x156152] << 24);
            printf("cycle %llu: early_init_dt_scan_root RETURN: addr_cells=%u size_cells=%u\n",
                   (unsigned long long)cycle, ac, sc);
        }
        // Also add a periodic dump during the scan_root window
        if (cycle >= 2614826 && cycle <= 2616000 && cycle % 100 == 0) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t ac = b0[0x156153] | (b1[0x156153] << 8) | (b2[0x156153] << 16) | (b3[0x156153] << 24);
            uint32_t sc = b0[0x156152] | (b1[0x156152] << 8) | (b2[0x156152] << 16) | (b3[0x156152] << 24);
            printf("cycle %llu: [periodic] dt_root: addr_cells=%u size_cells=%u PC=0x%08x\n",
                   (unsigned long long)cycle, ac, sc, pc);
        }
        // fdt_next_node entry (C011EBB8) - first 20 calls only
        {
            static int fdt_next_count = 0;
            if (pc == 0xC011EBB8 && fdt_next_count < 20) {
                fdt_next_count++;
                printf("cycle %llu: ENTERED fdt_next_node #%d\n",
                       (unsigned long long)cycle, fdt_next_count);
            }
        }
        // fdt_check_header entry (C011E794)
        if (pc == 0xC011E794) {
            printf("cycle %llu: ENTERED fdt_check_header\n", (unsigned long long)cycle);
        }
        // early_init_dt_verify entry (C015158C)
        if (pc == 0xC015158C) {
            printf("cycle %llu: ENTERED early_init_dt_verify\n", (unsigned long long)cycle);
        }
        // early_init_dt_scan_nodes entry (C01515D4)
        if (pc == 0xC01515D4) {
            printf("cycle %llu: ENTERED early_init_dt_scan_nodes\n", (unsigned long long)cycle);
        }
        // Decision points within early_init_dt_scan_memory:
        if (pc == 0xC01513F0) { // bgez s0 - check if fdt_first_subnode found a node
            printf("cycle %llu: dt_scan_memory: bgez node check\n", (unsigned long long)cycle);
        }
        if (pc == 0xC015144C) { // beqz a0 - device_type not found → skip
            printf("cycle %llu: dt_scan_memory: device_type check (beqz → skip if NULL)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC015145C) { // bnez a0 - strcmp result, not "memory" → skip
            printf("cycle %llu: dt_scan_memory: strcmp 'memory' check (bnez → skip if mismatch)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC015146C) { // beqz a0 - device not available → skip
            printf("cycle %llu: dt_scan_memory: availability check (beqz → skip if unavailable)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC0151488) { // bnez a0 - reg found → skip fallback
            printf("cycle %llu: dt_scan_memory: bnez a0 at C0151488 (reg found → jump to C01514A4)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC015148C) { // addi a2,sp,12 — only reached if reg==NULL (bnez not taken)
            printf("cycle %llu: dt_scan_memory: FALLTHROUGH to linux,usable-memory (reg was NULL!)\n",
                   (unsigned long long)cycle);
        }
        if (pc == 0xC01514A8) { // beqz s4 - reg property not found → skip
            printf("cycle %llu: dt_scan_memory: reg property check (beqz → skip if NULL)\n",
                   (unsigned long long)cycle);
        }
        // Track branch direction at reg property check: log next 3 PCs after beqz
        {
            static uint64_t reg_beqz_cycle = 0;
            static int reg_beqz_count = 0;
            if (pc == 0xC01514A8) {
                reg_beqz_cycle = cycle;
                reg_beqz_count++;
            }
            if (reg_beqz_cycle > 0 && cycle > reg_beqz_cycle && cycle <= reg_beqz_cycle + 5) {
                printf("  [REG-BEQZ #%d] cycle %llu: PC=0x%08x (after beqz at cycle %llu)\n",
                       reg_beqz_count, (unsigned long long)cycle, pc, (unsigned long long)reg_beqz_cycle);
            }
        }
        // === Comprehensive DMEM read trace for fdt_getprop("reg") window ===
        // This covers from availability check pass through the reg property check
        {
            static uint64_t avail_pass_cycle = 0;
            static int getprop_call_count_in_scan = 0;
            // Track when availability check passes (we know the next of_get_flat_dt_prop is for "reg")
            if (pc == 0xC015146C) {
                avail_pass_cycle = cycle;
            }
            // Count of_get_flat_dt_prop entries after availability passes
            if (avail_pass_cycle > 0 && pc == 0xC01508AC && cycle > avail_pass_cycle) {
                getprop_call_count_in_scan++;
                printf("  [GETPROP-REG] cycle %llu: of_get_flat_dt_prop call #%d after avail check (for 'reg')\n",
                       (unsigned long long)cycle, getprop_call_count_in_scan);
            }
            // Log ALL DMEM read addresses for 8000 cycles after availability check passes
            // (covers the reg property lookup completely)
            static int reg_trace_count = 0;
            if (avail_pass_cycle > 0 && cycle >= avail_pass_cycle && cycle < avail_pass_cycle + 8000
                && reg_trace_count < 2000) {
                uint32_t dmem_rd = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
                // Only log reads that touch the DTB area or look like stack/data accesses near kernel
                if (dmem_rd >= 0x3C0000 && dmem_rd < 0x3C1000) {
                    reg_trace_count++;
                    auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
                    auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
                    auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
                    auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
                    uint32_t word = b0[dmem_rd] | (b1[dmem_rd] << 8) |
                                    (b2[dmem_rd] << 16) | (b3[dmem_rd] << 24);
                    uint32_t dtb_byte_off = (dmem_rd - 0x3C0000) * 4;
                    printf("  [REG-DTB #%d] cycle %llu: rd_addr=0x%06x dtb_byte=0x%03x word=0x%08x PC=0x%08x\n",
                           reg_trace_count, (unsigned long long)cycle, dmem_rd, dtb_byte_off, word, pc);
                }
            }
        }
        // Trace ALU result, DMEM reads, and forwarding around bge check (C01514E0-C01514FC)
        if (pc >= 0xC01514D0 && pc <= 0xC0151510) {
#ifdef TRACE_INTERNAL_SIGNALS
            uint32_t alu_result = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_alu_result_approx;
            uint32_t rd_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
            uint8_t sup_exwb = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_suppressEXWB != 0;
            uint8_t stall_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_stall;
            uint8_t flush_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_flush;
            uint8_t div_stall = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_divStall != 0;
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t dmem_val = b0[rd_addr] | (b1[rd_addr] << 8) | (b2[rd_addr] << 16) | (b3[rd_addr] << 24);
            // Also read exwb_physAddr (forwarding address)
            uint32_t wr_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_dmem_write_addr;
            uint8_t wr_en0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte0_we;
            printf("  [BGE-TRACE] cy=%llu PC=0x%08x ALU=0x%08x rdAddr=0x%06x dmem=0x%08x sup=%d stall=%d flush=%d divS=%d wrEn=%d wrAddr=0x%06x\n",
                   (unsigned long long)cycle, pc, alu_result, rd_addr, dmem_val, sup_exwb, stall_sig, flush_sig, div_stall, wr_en0, wr_addr);
#endif
        }
        if (pc == 0xC01514F8) { // bge a5,a4 - cells remaining check
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t ac = b0[0x156153] | (b1[0x156153] << 8) | (b2[0x156153] << 16) | (b3[0x156153] << 24);
            uint32_t sc = b0[0x156152] | (b1[0x156152] << 8) | (b2[0x156152] << 16) | (b3[0x156152] << 24);
            printf("cycle %llu: dt_scan_memory: cells remaining check  addr_cells=%u size_cells=%u (needed=%u)\n",
                   (unsigned long long)cycle, ac, sc, ac + sc);
            // Dump stack area including fdt_get_property_namelen_ frame (s4 save at 0x160792)
            for (uint32_t a = 0x160790; a <= 0x1607A5; a++) {
                uint32_t v = b0[a] | (b1[a] << 8) | (b2[a] << 16) | (b3[a] << 24);
                uint32_t pa = 0x80000000 + a * 4;
                printf("  [STACK] DMEM[0x%06x] (PA 0x%08x) = 0x%08x\n", a, pa, v);
            }
        }
        // === Monitor DMEM write port during critical window ===
        // Track stores to stack area during of_get_flat_dt_prop and loop setup
        if (cycle >= 2740000 && cycle <= 2755000) {
#ifdef TRACE_INTERNAL_SIGNALS
            uint32_t wr_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_dmem_write_addr;
            uint8_t wr_en0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte0_we;
            // Only log writes to the stack area (DMEM 0x160790-0x1607B0)
            if (wr_en0 && wr_addr >= 0x160790 && wr_addr <= 0x1607B0) {
                auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
                auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
                auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
                auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
                uint32_t val_before = b0[wr_addr] | (b1[wr_addr] << 8) | (b2[wr_addr] << 16) | (b3[wr_addr] << 24);
                // Capture actual write data
                uint8_t wd0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte0_wdata;
                uint8_t wd1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte1_wdata;
                uint8_t wd2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte2_wdata;
                uint8_t wd3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_actual_byte3_wdata;
                uint32_t wr_data = wd0 | (wd1 << 8) | (wd2 << 16) | (wd3 << 24);
                printf("  [STACK-WR] cy=%llu PC=0x%08x wrAddr=0x%06x wrData=0x%08x (was 0x%08x)\n",
                       (unsigned long long)cycle, pc, wr_addr, wr_data, val_before);
            }
#endif
        }
        // (Old tight trace window removed — replaced by REG-DTB trace)
        // Also monitor DMEM writes to sp+8 and sp+12 area (reg_ptr and reg_len)
        // Track writes from of_get_flat_dt_prop return path
        if (pc == 0xC0151484 || pc == 0xC01514A0) {
            printf("cycle %llu: early_init_dt_scan_memory: sw a0,8(sp) at PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        if (pc == 0xC01514A4) {
            printf("cycle %llu: early_init_dt_scan_memory: lw s4,8(sp) at PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        if (pc == 0xC01514AC) {
            // Capture dmem_read_addr when lw a5,12(sp) is in IF — the actual read happens ~1-2 cycles later
            printf("cycle %llu: early_init_dt_scan_memory: lw a5,12(sp) [reg_len] at PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        // Trace DMEM reads around reg_len load (cycles 2747495-2747510 and 2754530-2754560)
        if ((cycle >= 2747495 && cycle <= 2747510) || (cycle >= 2754530 && cycle <= 2754560)) {
            uint32_t rd = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t val = b0[rd] | (b1[rd] << 8) | (b2[rd] << 16) | (b3[rd] << 24);
            printf("  [REG-LEN] cy=%llu PC=0x%08x rdAddr=0x%06x dmem[rdAddr]=0x%08x\n",
                   (unsigned long long)cycle, pc, rd, val);
        }
        // Monitor key PCs in early_init_dt_scan_memory loop body
        if (pc == 0xC01514C4) {
            printf("cycle %llu: early_init_dt_scan_memory: add s4,s4,a5 [s4=end_ptr] at PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        if (pc == 0xC01514E0) {
            // Loop entry: lw a5,8(sp) — read current reg pointer
            uint32_t rd = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
            printf("cycle %llu: early_init_dt_scan_memory loop iteration (rdAddr=0x%06x)\n",
                   (unsigned long long)cycle, rd);
        }
        // dt_mem_next_cell calls: C0151510 (parse base), C0151528 (parse size)
        if (pc == 0xC0151510) {
            printf("cycle %llu: dt_mem_next_cell for BASE (C0151510)\n", (unsigned long long)cycle);
        }
        if (pc == 0xC0151518) {
            printf("cycle %llu: after BASE: mv s2,a0 (C0151518)\n", (unsigned long long)cycle);
        }
        if (pc == 0xC0151528) {
            printf("cycle %llu: dt_mem_next_cell for SIZE (C0151528)\n", (unsigned long long)cycle);
        }
        // Detailed PC trace from loop body start through dt_mem_next_cell return
        {
            static uint64_t loop_body_start = 0;
            if (pc == 0xC0151510 && loop_body_start == 0 && cycle > 2750000) {
                loop_body_start = cycle;
                printf("  === LOOP BODY TRACE START (cycle %llu) ===\n", (unsigned long long)cycle);
            }
            if (loop_body_start > 0 && cycle >= loop_body_start && cycle < loop_body_start + 200) {
                static uint32_t last_lbt_pc = 0;
                if (pc != last_lbt_pc) {
#ifdef TRACE_INTERNAL_SIGNALS
                    uint8_t flush_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_flush;
                    uint8_t stall_sig = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_stall;
                    uint8_t sup_exwb = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_suppressEXWB != 0;
                    printf("  [LBT] cy=%llu PC=0x%08x flush=%d stall=%d supEXWB=%d\n",
                           (unsigned long long)cycle, pc, flush_sig, stall_sig, sup_exwb);
#else
                    printf("  [LBT] cy=%llu PC=0x%08x\n", (unsigned long long)cycle, pc);
#endif
                    last_lbt_pc = pc;
                }
            }
        }
        // size==0 check: C0151538 beqz a5
        if (pc == 0xC0151538) {
            printf("cycle %llu: dt_scan_memory: size==0 check (beqz, skip if zero)\n", (unsigned long long)cycle);
        }
        // The actual call to early_init_dt_add_memory_arch: C015154C
        if (pc == 0xC015154C) {
            printf("cycle %llu: CALLING early_init_dt_add_memory_arch (C015154C) *** THIS IS THE REAL CALL ***\n",
                   (unsigned long long)cycle);
        }
        // Detailed trace around reg_len load and cells check
        if ((cycle >= 2747495 && cycle <= 2747520) || (cycle >= 2754530 && cycle <= 2754560)) {
            uint32_t dmem_rd = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t rd_val = b0[dmem_rd] | (b1[dmem_rd] << 8) | (b2[dmem_rd] << 16) | (b3[dmem_rd] << 24);
            printf("  [REG-LEN] cycle %llu: PC=0x%08x dmem_rd=0x%06x val=0x%08x\n",
                   (unsigned long long)cycle, pc, dmem_rd, rd_val);
        }
        // === Comprehensive MMU/TLB trace around the bad translation ===
        // Window 1: cycles 2747495-2747520 (GOOD translation of DTB reg data)
        // Window 2: cycles 2754530-2754560 (BAD translation - DMEM addr 0x7FFFFF)
        // Window 3: PTW activity between (eviction of TLB entry)
        if ((cycle >= 2747495 && cycle <= 2747520) ||
            (cycle >= 2754530 && cycle <= 2754560) ||
            // Also trace any cycle where ptwStateNext != 0 in the gap
            (cycle >= 2747520 && cycle <= 2754560 &&
             dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_ptwStateNext != 0)) {
            uint32_t dmem_rd = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dmem_read_addr;
            uint8_t use_translated = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_useTranslatedAddr;
            uint8_t dtlb_miss = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dTLBMiss;
            uint32_t eff_addr = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_effectiveAddr;
            uint32_t dphys = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_dPhysAddr;
            uint32_t alu_approx = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_alu_result_approx;
            uint8_t ptw_state_next = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_ptwStateNext;
            uint8_t ptw_req = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_ptwReq;
            uint8_t stall = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_stall;
            uint8_t flush = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_flush;
            uint8_t flush_delay = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_flushOrDelay;
            uint8_t suppress = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_suppressEXWB;
            printf("  [MMU] cy=%llu PC=0x%08x dmem=0x%06x useTr=%d dMiss=%d eff=0x%08x dPhy=0x%08x aluA=0x%08x ptwSN=%d ptwR=%d st=%d fl=%d sup=%d\n",
                   (unsigned long long)cycle, pc, dmem_rd, use_translated, dtlb_miss,
                   eff_addr, dphys, alu_approx, ptw_state_next, ptw_req, stall, flush, suppress);
        }
        if (pc == 0xC01514C4) {
            printf("cycle %llu: early_init_dt_scan_memory: add s4,s4,a5 [s4=end_ptr] at PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        // C0151430: node processing start (after bgez taken)
        if (pc == 0xC0151430) {
            printf("cycle %llu: dt_scan_memory: NODE PROCESSING START (C0151430)\n",
                   (unsigned long long)cycle);
        }
        // of_get_flat_dt_prop (C01508AC) - but only when called from dt_scan_memory
        // (track broadly since it's called from multiple places)
        if (pc == 0xC01508AC) {
            printf("cycle %llu: ENTERED of_get_flat_dt_prop\n", (unsigned long long)cycle);
        }
        // C01513F4: return path (bgez not taken, no more nodes)
        if (pc == 0xC01513F4) {
            printf("cycle %llu: dt_scan_memory: RETURN (no more nodes)\n",
                   (unsigned long long)cycle);
        }
        // Full PC trace for 500 cycles when dt_scan_memory enters node processing
        static uint64_t node_proc_cycle = 0;
        static int node_proc_count = 0;
        if (pc == 0xC0151430) {
            node_proc_count++;
            node_proc_cycle = cycle;
        }
        if (node_proc_cycle > 0 && cycle >= node_proc_cycle && cycle < node_proc_cycle + 30 && node_proc_count <= 2) {
            printf("  NP[%d] cycle %llu: PC=0x%08x\n",
                   node_proc_count, (unsigned long long)cycle, pc);
        }
        // Monitor early_init_dt_add_memory_arch (C0151238)
        // Ring buffer of last 50 PCs
        static uint32_t pc_ring[50];
        static uint64_t cycle_ring[50];
        static int ring_idx = 0;
        pc_ring[ring_idx] = pc;
        cycle_ring[ring_idx] = cycle;
        ring_idx = (ring_idx + 1) % 50;

        static int dt_add_mem_call_count = 0;
        // Check for ACTUAL call site: JAL at C015154C that calls early_init_dt_add_memory_arch
        if (pc == 0xC015154C) {
            printf("cycle %llu: CALL SITE for early_init_dt_add_memory_arch (JAL at C015154C)\n",
                   (unsigned long long)cycle);
        }
        // Check for deep instruction (C0151258) that proves function body is actually executing
        if (pc == 0xC0151258) {
            dt_add_mem_call_count++;
            printf("cycle %llu: early_init_dt_add_memory_arch CONFIRMED executing #%d (PC=C0151258)\n",
                   (unsigned long long)cycle, dt_add_mem_call_count);
        }
        // Check pcReg == C0151238 (may be false positive from JAL at C0151234)
        if (pc == 0xC0151238) {
            printf("cycle %llu: pcReg=C0151238 (may be false positive from preceding JAL)\n",
                   (unsigned long long)cycle);
        }
        // Also check early_init_dt_scan_memory key PCs
        // C01514E0: loop start (for each property)
        if (pc == 0xC01514E0) {
            printf("cycle %llu: early_init_dt_scan_memory loop iteration\n",
                   (unsigned long long)cycle);
        }
        // C01514FC: found memory node, calling fdt_next_subnode
        if (pc == 0xC01514FC) {
            printf("cycle %llu: early_init_dt_scan_memory calling fdt_next_subnode\n",
                   (unsigned long long)cycle);
        }
        // C0151538: beqz a5 (size check before calling dt_add_memory_arch)
        if (pc == 0xC0151538) {
            printf("cycle %llu: early_init_dt_scan_memory beqz size check\n",
                   (unsigned long long)cycle);
        }
        // Monitor setup_arch (C0143390)
        if (pc == 0xC0143390) {
            printf("cycle %llu: ENTERED setup_arch PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }
        // Monitor parse_dtb-related functions
        if (pc == 0xC015160C) {
            printf("cycle %llu: ENTERED early_init_dt_scan PC=0x%08x\n",
                   (unsigned long long)cycle, pc);
        }

        // === Dump modified DTB to file at cycle 2600000 (before kernel parsing) ===
        if (cycle == 2600000 && !dtb_path.empty()) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            // Read DTB total_size from header (big-endian, word 1)
            uint8_t ts0 = b0[0x3C0001], ts1 = b1[0x3C0001], ts2 = b2[0x3C0001], ts3 = b3[0x3C0001];
            uint32_t dtb_total_size = (ts0 << 24) | (ts1 << 16) | (ts2 << 8) | ts3;
            printf("cycle 2600000: Dumping modified DTB (total_size=%u bytes) to /tmp/modified_dtb.bin\n", dtb_total_size);
            if (dtb_total_size > 0 && dtb_total_size < 65536) {
                FILE* f = fopen("/tmp/modified_dtb.bin", "wb");
                if (f) {
                    for (uint32_t i = 0; i < (dtb_total_size + 3) / 4; i++) {
                        uint32_t addr = 0x3C0000 + i;
                        uint8_t bytes[4] = { (uint8_t)b0[addr], (uint8_t)b1[addr], (uint8_t)b2[addr], (uint8_t)b3[addr] };
                        size_t to_write = (i * 4 + 4 <= dtb_total_size) ? 4 : dtb_total_size - i * 4;
                        fwrite(bytes, 1, to_write, f);
                    }
                    fclose(f);
                    printf("  Written %u bytes to /tmp/modified_dtb.bin\n", dtb_total_size);
                }
            }
            // Also dump kernel_map at this point
            printf("  kernel_map dump at cycle 2600000:\n");
            for (int i = 0; i < 7; i++) {
                uint32_t w = 0x15F946 + i;
                uint32_t val = b0[w] | (b1[w] << 8) | (b2[w] << 16) | (b3[w] << 24);
                printf("    +%2d (word 0x%06x) = 0x%08x\n", i*4, w, val);
            }
        }

        // === DTB runtime integrity check ===
        // Correct DTB values: [0x8D]=0x6f6d656d("memo"), [0x8F]=0x03000000(FDT_PROP), [0x90]=0x08000000(len=8), [0x92]=0x00000080(base lo)
        if (cycle <= 10 || cycle == 100 || cycle == 1000 || cycle == 10000 || cycle == 100000 || cycle == 500000 || cycle == 1000000 || cycle == 2614000) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            uint32_t dtb_w8F = b0[0x3C008F] | (b1[0x3C008F] << 8) | (b2[0x3C008F] << 16) | (b3[0x3C008F] << 24);
            uint32_t dtb_w90 = b0[0x3C0090] | (b1[0x3C0090] << 8) | (b2[0x3C0090] << 16) | (b3[0x3C0090] << 24);
            uint32_t dtb_w92 = b0[0x3C0092] | (b1[0x3C0092] << 8) | (b2[0x3C0092] << 16) | (b3[0x3C0092] << 24);
            uint32_t dtb_w93 = b0[0x3C0093] | (b1[0x3C0093] << 8) | (b2[0x3C0093] << 16) | (b3[0x3C0093] << 24);
            bool ok8F = (dtb_w8F == 0x03000000);
            bool ok90 = (dtb_w90 == 0x08000000);
            bool ok92 = (dtb_w92 == 0x00000080);
            bool ok93 = (dtb_w93 == 0x00000002);
            printf("cycle %llu: DTB [0x8F]=0x%08x(%s) [0x90]=0x%08x(%s) [0x92]=0x%08x(%s) [0x93]=0x%08x(%s)\n",
                   (unsigned long long)cycle, dtb_w8F, ok8F?"OK":"BAD", dtb_w90, ok90?"OK":"BAD",
                   dtb_w92, ok92?"OK":"BAD", dtb_w93, ok93?"OK":"BAD");
        }

        // === Early memblock dump (around second SATP switch) ===
        if (cycle == 2610000 || cycle == 2654500 || cycle == 2700000 || cycle == 2760000 || cycle == 3000000 || cycle == 3200000) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            // memblock.memory @ word 0x156157 (cnt), 0x156158 (max), 0x156159 (total_size)
            uint32_t cnt = b0[0x156157] | (b1[0x156157] << 8) | (b2[0x156157] << 16) | (b3[0x156157] << 24);
            uint32_t total = b0[0x156159] | (b1[0x156159] << 8) | (b2[0x156159] << 16) | (b3[0x156159] << 24);
            // region[0] @ word 0x156166
            uint32_t rbase = b0[0x156166] | (b1[0x156166] << 8) | (b2[0x156166] << 16) | (b3[0x156166] << 24);
            uint32_t rsize = b0[0x156167] | (b1[0x156167] << 8) | (b2[0x156167] << 16) | (b3[0x156167] << 24);
            printf("cycle %llu: memblock.memory: cnt=%u total=0x%08x region[0]={base=0x%08x,size=0x%08x}\n",
                   (unsigned long long)cycle, cnt, total, rbase, rsize);
            // Also dump raw 8 words around init_regions
            printf("  raw DMEM around init_regions (word 0x156164-0x15616B):\n");
            for (int w = 0x156164; w <= 0x15616B; w++) {
                uint32_t val = b0[w] | (b1[w] << 8) | (b2[w] << 16) | (b3[w] << 24);
                printf("    word[0x%06x] = 0x%08x\n", w, val);
            }
            // Dump kernel_map struct @ C017E518, PA 0x8057E518, word 0x15F946
            // page_offset(+0), virt_addr(+4), phys_addr(+8), size(+12), va_pa_offset(+16), pgd(+20)
            printf("  kernel_map:\n");
            for (int i = 0; i < 7; i++) {
                uint32_t w = 0x15F946 + i;
                uint32_t val = b0[w] | (b1[w] << 8) | (b2[w] << 16) | (b3[w] << 24);
                const char* names[] = {"page_offset", "virt_addr", "phys_addr", "size", "va_pa_offset", "pgd", "???"};
                printf("    +%2d (word 0x%06x) = 0x%08x  (%s)\n", i*4, w, val, names[i]);
            }
            // Dump dt_root_addr_cells @ word 0x156153, dt_root_size_cells @ word 0x156152
            uint32_t addr_cells = b0[0x156153] | (b1[0x156153] << 8) | (b2[0x156153] << 16) | (b3[0x156153] << 24);
            uint32_t size_cells = b0[0x156152] | (b1[0x156152] << 8) | (b2[0x156152] << 16) | (b3[0x156152] << 24);
            printf("  dt_root_addr_cells=%u dt_root_size_cells=%u\n", addr_cells, size_cells);
            // Dump initial_boot_params @ C017E678, PA 0x8057E678, word 0x15F99E
            uint32_t ibp = b0[0x15F99E] | (b1[0x15F99E] << 8) |
                           (b2[0x15F99E] << 16) | (b3[0x15F99E] << 24);
            printf("  initial_boot_params=0x%08x\n", ibp);
            // Verify DTB content at PA 0x80F00000 (word addr 0x3C0000)
            // FDT magic = 0xD00DFEED (big-endian) → little-endian word = 0xEDFE0DD0
            printf("  DTB @ word 0x3C0000 (PA 0x80F00000): magic=0x%02x%02x%02x%02x",
                   b3[0x3C0000], b2[0x3C0000], b1[0x3C0000], b0[0x3C0000]);
            uint32_t dtb_w0 = b0[0x3C0000] | (b1[0x3C0000] << 8) | (b2[0x3C0000] << 16) | (b3[0x3C0000] << 24);
            printf(" (word=0x%08x)\n", dtb_w0);
            // Dump first 4 DTB words
            for (int w = 0; w < 8; w++) {
                uint32_t a = 0x3C0000 + w;
                uint32_t val = b0[a] | (b1[a] << 8) | (b2[a] << 16) | (b3[a] << 24);
                printf("    DTB[%d] @ 0x%06x = 0x%08x\n", w, a, val);
            }
        }

        // === Dump memory_limit and key variables before SATP switch #3 ===
        if (cycle == 3328500) {
            auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
            auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
            auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
            auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
            // memory_limit @ virt 0xC01F406C, word addr 0x17D01B
            uint32_t mlimit = b0[0x17D01B] | (b1[0x17D01B] << 8) |
                              (b2[0x17D01B] << 16) | (b3[0x17D01B] << 24);
            // kernel_map.va_pa_offset @ nm 0xC017E518, offset from _start = 0x17E518
            // PA = 0x80400000 + 0x17E518 = 0x8057E518, word = 0x57E518/4 = 0x15F946
            // kernel_map struct: phys_addr(+0), size(+4), page_offset(+8), va_pa_offset(+12)
            uint32_t vapaoff = b0[0x15F946+3] | (b1[0x15F946+3] << 8) |
                               (b2[0x15F946+3] << 16) | (b3[0x15F946+3] << 24);
            printf("cycle 3328500: memory_limit=0x%08x va_pa_offset=0x%08x\n", mlimit, vapaoff);

            // === Dump memblock data structure ===
            // memblock @ C0158554, PA 0x80558554, word_addr = 0x156155
            // struct memblock { bool bottom_up(+0), phys_addr_t current_limit(+4),
            //   memblock_type memory(+8), memblock_type reserved(+28) }
            // struct memblock_type { cnt(+0), max(+4), total_size(+8), *regions(+12), *name(+16) }
            // sizeof(memblock_type) = 20
            uint32_t mb_bottom_up = b0[0x156155] | (b1[0x156155] << 8) |
                                    (b2[0x156155] << 16) | (b3[0x156155] << 24);
            uint32_t mb_current_limit = b0[0x156156] | (b1[0x156156] << 8) |
                                        (b2[0x156156] << 16) | (b3[0x156156] << 24);
            uint32_t mb_mem_cnt = b0[0x156157] | (b1[0x156157] << 8) |
                                  (b2[0x156157] << 16) | (b3[0x156157] << 24);
            uint32_t mb_mem_max = b0[0x156158] | (b1[0x156158] << 8) |
                                  (b2[0x156158] << 16) | (b3[0x156158] << 24);
            uint32_t mb_mem_total = b0[0x156159] | (b1[0x156159] << 8) |
                                    (b2[0x156159] << 16) | (b3[0x156159] << 24);
            uint32_t mb_mem_regions = b0[0x15615A] | (b1[0x15615A] << 8) |
                                      (b2[0x15615A] << 16) | (b3[0x15615A] << 24);
            printf("  memblock: bottom_up=0x%08x current_limit=0x%08x\n", mb_bottom_up, mb_current_limit);
            printf("  memblock.memory: cnt=%u max=%u total_size=0x%08x regions=0x%08x\n",
                   mb_mem_cnt, mb_mem_max, mb_mem_total, mb_mem_regions);

            // Dump first 4 memory regions from memblock_memory_init_regions
            // @ C0158598, PA 0x80558598, word_addr = 0x156166
            // sizeof(memblock_region) = 12 bytes (base+4, size+4, flags+4) = 3 words
            printf("  memblock.memory regions (from init_regions @ 0x156166):\n");
            for (int i = 0; i < 4; i++) {
                uint32_t rw = 0x156166 + i * 3;
                uint32_t rbase = b0[rw] | (b1[rw] << 8) | (b2[rw] << 16) | (b3[rw] << 24);
                uint32_t rsize = b0[rw+1] | (b1[rw+1] << 8) | (b2[rw+1] << 16) | (b3[rw+1] << 24);
                uint32_t rflags = b0[rw+2] | (b1[rw+2] << 8) | (b2[rw+2] << 16) | (b3[rw+2] << 24);
                if (rbase != 0 || rsize != 0)
                    printf("    region[%d]: base=0x%08x size=0x%08x flags=0x%08x (end=0x%08x)\n",
                           i, rbase, rsize, rflags, rbase + rsize);
            }
            // Also dump via the regions pointer (in case it points elsewhere)
            if (mb_mem_regions >= 0xC0000000 && mb_mem_regions < 0xC0200000) {
                uint32_t reg_pa = (mb_mem_regions - 0xC0000000) + 0x80400000;
                uint32_t reg_word = (reg_pa - 0x80000000) / 4;
                printf("  memblock.memory regions (via pointer 0x%08x, PA 0x%08x, word 0x%06x):\n",
                       mb_mem_regions, reg_pa, reg_word);
                for (int i = 0; i < 4; i++) {
                    uint32_t rw = reg_word + i * 3;
                    uint32_t rbase = b0[rw] | (b1[rw] << 8) | (b2[rw] << 16) | (b3[rw] << 24);
                    uint32_t rsize = b0[rw+1] | (b1[rw+1] << 8) | (b2[rw+1] << 16) | (b3[rw+1] << 24);
                    uint32_t rflags = b0[rw+2] | (b1[rw+2] << 8) | (b2[rw+2] << 16) | (b3[rw+2] << 24);
                    if (rbase != 0 || rsize != 0)
                        printf("    region[%d]: base=0x%08x size=0x%08x flags=0x%08x (end=0x%08x)\n",
                               i, rbase, rsize, rflags, rbase + rsize);
                }
            }

            // Also dump swapper_pg_dir[0x300] = word addr 0x17DF00
            uint32_t pgd300 = b0[0x17DF00] | (b1[0x17DF00] << 8) |
                              (b2[0x17DF00] << 16) | (b3[0x17DF00] << 24);
            printf("  swapper_pg_dir[0x300] = 0x%08x\n", pgd300);
            // Dump entire swapper_pg_dir non-zero entries (VPN1 >= 0x200)
            for (int i = 0x200; i <= 0x3FF; i++) {
                uint32_t addr = 0x17DC00 + i;  // swapper_pg_dir base + pgd_index
                uint32_t val = b0[addr] | (b1[addr] << 8) | (b2[addr] << 16) | (b3[addr] << 24);
                if (val != 0)
                    printf("  swapper_pg_dir[0x%03x] = 0x%08x\n", i, val);
            }
        }

        // Log when PTW PTE changes (PTW read a new PTE from DMEM)
        static uint32_t prev_ptw_pte = 0;
        if (ptw_pte != prev_ptw_pte) {
            printf("cycle %llu: PTW-PTE: 0x%08x -> 0x%08x  vaddr=0x%08x PC=0x%08x satp=0x%08x\n",
                   (unsigned long long)cycle, prev_ptw_pte, ptw_pte, ptw_vaddr, pc, satp_reg);
            prev_ptw_pte = ptw_pte;
        }
        // Log when PTW vaddr changes (new PTW walk started)
        static uint32_t prev_ptw_vaddr = 0;
        if (ptw_vaddr != prev_ptw_vaddr) {
            printf("cycle %llu: PTW-WALK: vaddr 0x%08x -> 0x%08x  PC=0x%08x satp=0x%08x\n",
                   (unsigned long long)cycle, prev_ptw_vaddr, ptw_vaddr, pc, satp_reg);
            prev_ptw_vaddr = ptw_vaddr;
        }
        // Log when satp changes (page table root switch)
        static uint32_t prev_satp_log = 0;
        if (satp_reg != prev_satp_log) {
            printf("cycle %llu: SATP: 0x%08x -> 0x%08x  PC=0x%08x\n",
                   (unsigned long long)cycle, prev_satp_log, satp_reg, pc);
            // Dump L1 PTEs for VPN1=0x300..0x303 from the NEW page table
            if (satp_reg & 0x80000000) {
                uint32_t ppn = satp_reg & 0x3FFFFF;
                for (int vpn1 = 0x200; vpn1 <= 0x303; vpn1++) {
                    // L1 PTE address = ppn * 4096 + vpn1 * 4
                    uint32_t pte_phys = (ppn << 12) + (vpn1 * 4);
                    uint32_t word_addr = ((pte_phys - 0x80000000) >> 2) & 0x7FFFFF;
                    if (word_addr < 8388608) {
                        auto& b0 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte0_rdata;
                        auto& b1 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte1_rdata;
                        auto& b2 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte2_rdata;
                        auto& b3 = dut->rootp->rv32i_soc__DOT__gen_soc__DOT___gen_byte3_rdata;
                        uint32_t pte = b0[word_addr] | (b1[word_addr] << 8) |
                                       (b2[word_addr] << 16) | (b3[word_addr] << 24);
                        if (pte != 0) {
                            printf("  PTE[0x%03x] @ phys 0x%08x (word 0x%06x) = 0x%08x\n",
                                   vpn1, pte_phys, word_addr, pte);
                        }
                    }
                }
            }
            prev_satp_log = satp_reg;
        }

        // Trap/iTLB debug logging (disabled for clean output)

        // UART output
        if (uart_valid) {
            uart_log.push_back(uart_data);

            if (opensbi_mode) {
                // OpenSBI mode: print characters (byte in data[7:0])
                uint8_t ch = uart_data & 0xFF;
                if (ch >= 0x20 && ch <= 0x7E) {
                    putchar(ch);
                } else if (ch == '\n') {
                    putchar('\n');
                } else if (ch == '\r') {
                    // ignore CR
                } else {
                    printf("[0x%02x]", ch);
                }
                fflush(stdout);
            } else {
                // Firmware test mode: print hex words
                printf("  UART[%zu]: 0x%08x\n", uart_log.size(), uart_data);
                // Stop shortly after pass/fail marker
                if (uart_data == 0xCAFE0000u || uart_data == 0xDEADDEADu) {
                    // Run a few more cycles to drain the pipeline
                    for (int drain = 0; drain < 20; drain++) {
                        dut->clk = 0; dut->eval(); time_ps++;
                        dut->clk = 1; dut->eval(); time_ps++;
                        if (dut->uart_tx_valid) {
                            uart_log.push_back(dut->uart_tx_data);
                            printf("  UART[%zu]: 0x%08x\n", uart_log.size(), dut->uart_tx_data);
                        }
                    }
                    printf("Simulation complete at cycle %llu\n",
                           (unsigned long long)cycle);
                    break;
                }
            }
        }

        // Halt detection (self-loop)
        if (pc == prev_pc) {
            halt_count++;
            if (halt_count >= 50) {
                printf("\nHalt detected at cycle %llu: PC = 0x%08x\n",
                       (unsigned long long)cycle, pc);
                break;
            }
        } else {
            halt_count = 0;
        }
        prev_pc = pc;

        // Falling edge
        dut->clk = 0;
        dut->eval();
        time_ps++;
        if (vcd) vcd->dump(time_ps);
    }

    // Print summary
    if (opensbi_mode) {
        printf("\n=== OpenSBI simulation ended (%zu UART bytes) ===\n", uart_log.size());
    } else {
        printf("\n=== UART Output (%zu words) ===\n", uart_log.size());
        for (size_t i = 0; i < uart_log.size(); i++) {
            printf("  0x%08x\n", uart_log[i]);
        }

        // Check pass/fail markers
        bool found_pass = false, found_fail = false;
        for (auto v : uart_log) {
            if (v == 0xCAFE0000u) found_pass = true;
            if (v == 0xDEADDEADu) found_fail = true;
        }
        if (found_pass) printf("\n*** ALL TESTS PASSED ***\n");
        else if (found_fail) printf("\n*** SOME TESTS FAILED ***\n");
        else printf("\n*** No pass/fail marker found ***\n");

        // Cleanup
        if (vcd) { vcd->close(); delete vcd; }
        delete dut;
        return found_pass ? 0 : 1;
    }

    // Cleanup
    if (vcd) { vcd->close(); delete vcd; }
    delete dut;
    return 0;
}
