// Sparkle Drone Verilator Co-Sim Harness — Parallel I/O Version
//
// Drives sprayDroneSoCParallel via direct signal writes (no SPI/UART/
// SBUS bit-banging). Reads sensors from shared memory, writes actuators
// back. Synchronizes with Gazebo via two atomic flags.
//
// Build:
//   verilator --cc --exe --build -j 4 -O3 \
//     --top-module Sparkle_IP_Drone_sprayDroneSoCParallel \
//     generated_drone_parallel.sv verilator_cosim_parallel.cpp \
//     -o obj_dir/sparkle_drone_cosim -CFLAGS "-I$(pwd)"
//
// Run:
//   ./obj_dir/sparkle_drone_cosim [max_steps]

#include "cosim_shmem.h"
#include "VSparkle_IP_Drone_sprayDroneSoCParallel.h"

#include <verilated.h>

#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <atomic>
#include <thread>
#include <chrono>
#include <memory>

// === Output bundle bit layout (53-bit 'out' port) ===
// [52:42] t1 (11-bit throttle, motor 1)
// [41:31] t2 (11-bit throttle, motor 2)
// [30:20] t3 (11-bit throttle, motor 3)
// [19:9]  t4 (11-bit throttle, motor 4)
// [8]     pump1
// [7]     pump2
// [6]     pump3
// [5]     pump4
// [4]     missionDone
// [3:0]   fsCode (4-bit failsafe code)

static uint16_t extract_throttle(uint64_t out_bundle, int motor_idx) {
    int shift = 42 - motor_idx * 11;
    return (uint16_t)((out_bundle >> shift) & 0x7FF);
}

static bool extract_pump(uint64_t out_bundle, int pump_idx) {
    return (bool)((out_bundle >> (8 - pump_idx)) & 1);
}

static bool extract_mission_done(uint64_t out_bundle) {
    return (bool)((out_bundle >> 4) & 1);
}

static uint8_t extract_fs_code(uint64_t out_bundle) {
    return (uint8_t)(out_bundle & 0xF);
}

// DShot throttle (48-2047) → PWM duty ratio
static float dshot_to_normalized(uint16_t throttle) {
    if (throttle <= 48) return 0.0f;
    if (throttle >= 2047) return 1.0f;
    return (float)(throttle - 48) / 1999.0f;
}

static sparkle_cosim_t* shm_ptr = nullptr;

static auto flag(uint32_t* p) {
    return reinterpret_cast<std::atomic<uint32_t>*>(p);
}

static bool setup_shm() {
    int fd = shm_open(SPARKLE_COSIM_SHM_PATH, O_CREAT | O_RDWR, 0666);
    if (fd < 0) { perror("shm_open"); return false; }
    if (ftruncate(fd, SPARKLE_COSIM_SHM_SIZE) < 0) {
        perror("ftruncate"); close(fd); return false;
    }
    void* ptr = mmap(nullptr, SPARKLE_COSIM_SHM_SIZE,
                     PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (ptr == MAP_FAILED) { perror("mmap"); return false; }
    shm_ptr = (sparkle_cosim_t*)ptr;
    if (shm_ptr->magic != SPARKLE_COSIM_MAGIC) {
        memset(shm_ptr, 0, SPARKLE_COSIM_SHM_SIZE);
        shm_ptr->magic = SPARKLE_COSIM_MAGIC;
        shm_ptr->version = SPARKLE_COSIM_VERSION;
    }
    return true;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    int max_steps = 0;  // 0 = forever
    if (argc > 1) max_steps = atoi(argv[1]);

    if (!setup_shm()) return 1;

    auto dut = std::make_unique<VSparkle_IP_Drone_sprayDroneSoCParallel>();

    // Reset
    dut->rst = 1;
    dut->clk = 0;
    dut->eval();
    for (int i = 0; i < 10; i++) {
        dut->clk = 1; dut->eval();
        dut->clk = 0; dut->eval();
    }
    dut->rst = 0;

    printf("Sparkle parallel-I/O co-sim ready on %s\n", SPARKLE_COSIM_SHM_PATH);
    printf("Waiting for Gazebo sensor updates...\n");

    uint64_t step_count = 0;
    auto t_start = std::chrono::steady_clock::now();

    while (max_steps == 0 || (int64_t)step_count < max_steps) {
        // Wait for Gazebo to publish sensors
        while (flag(&shm_ptr->sensors_ready)->load(std::memory_order_acquire) == 0) {
            if (Verilated::gotFinish()) break;
            std::this_thread::sleep_for(std::chrono::microseconds(5));
        }
        if (Verilated::gotFinish()) break;

        // === Copy sensors from shm into Verilated DUT signals ===
        dut->_gen_accelX = (uint32_t)shm_ptr->accel_x;
        dut->_gen_accelY = (uint32_t)shm_ptr->accel_y;
        dut->_gen_accelZ = (uint32_t)shm_ptr->accel_z;
        dut->_gen_gyroX  = (uint32_t)shm_ptr->gyro_x;
        dut->_gen_gyroY  = (uint32_t)shm_ptr->gyro_y;
        dut->_gen_gyroZ  = (uint32_t)shm_ptr->gyro_z;
        dut->_gen_gpsLat = (uint32_t)shm_ptr->gps_lat;
        dut->_gen_gpsLon = (uint32_t)shm_ptr->gps_lon;
        dut->_gen_gpsAlt = (uint32_t)shm_ptr->gps_alt;
        dut->_gen_gpsValid = shm_ptr->gps_valid ? 1 : 0;
        dut->_gen_batteryLow = shm_ptr->battery_low ? 1 : 0;
        dut->_gen_rcFailsafe = shm_ptr->rc_failsafe ? 1 : 0;
        dut->_gen_obstacleDetect = shm_ptr->obstacle_detected ? 1 : 0;
        dut->_gen_armSwitch = 1;
        dut->_gen_missionGo = 1;

        flag(&shm_ptr->sensors_ready)->store(0, std::memory_order_release);

        // === Step SoC for one control cycle ===
        // 1 control cycle = 1 clock edge for combinational outputs
        // (register-based components update on clock edges too)
        dut->clk = 1; dut->eval();
        dut->clk = 0; dut->eval();

        // === Extract outputs from 53-bit 'out' bundle ===
        uint64_t out = 0;
        // Verilator packs >32-bit outputs into an array; check size
        // For 53-bit 'out', it's stored in a VlWide or uint64_t depending on version.
        // Assuming 64-bit storage for simplicity:
        out = (uint64_t)dut->out;

        for (int m = 0; m < 4; m++) {
            uint16_t throttle = extract_throttle(out, m);
            shm_ptr->motor_throttle[m] = throttle;
            // Pump duty: enable flag × full duty, or 0
            bool pump_on = extract_pump(out, m);
            shm_ptr->pump_duty[m] = pump_on ? 0xFFFF : 0x0000;
        }
        shm_ptr->mission_done = extract_mission_done(out) ? 1 : 0;
        shm_ptr->failsafe_code = extract_fs_code(out);
        shm_ptr->cycle_count = step_count;

        flag(&shm_ptr->actuators_ready)->store(1, std::memory_order_release);

        step_count++;

        // Progress report every 10000 steps
        if (step_count % 10000 == 0) {
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - t_start).count();
            double rate = step_count / elapsed;
            printf("[cosim-parallel] step=%llu rate=%.0f steps/s thr=%u fs=%u\n",
                   (unsigned long long)step_count, rate,
                   shm_ptr->motor_throttle[0], shm_ptr->failsafe_code);
        }
    }

    auto t_end = std::chrono::steady_clock::now();
    double total_s = std::chrono::duration<double>(t_end - t_start).count();
    printf("[cosim-parallel] Done: %llu steps in %.2f s (%.0f steps/s)\n",
           (unsigned long long)step_count, total_s,
           total_s > 0 ? step_count / total_s : 0.0);

    dut->final();
    return 0;
}
