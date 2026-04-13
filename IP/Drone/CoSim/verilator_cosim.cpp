// Sparkle Drone Verilator Co-Sim Harness
//
// Connects the Verilated Sparkle drone SoC to Ignition Gazebo via
// POSIX shared memory. Runs in a loop, synchronized with the physics
// simulator through sensors_ready / actuators_ready flags.
//
// Build:
//   verilator --cc --exe --build -j 4 -O3 \
//     --top-module Sparkle_IP_Drone_sprayDroneSoC \
//     generated_drone_soc.sv verilator_cosim.cpp -o cosim
//
// Run:
//   ./cosim           # waits for Gazebo to attach
//
// Gazebo plugin must map /sparkle_drone_cosim first.

#include "cosim_shmem.h"

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

// Verilator-generated header (replace with actual module name)
// #include "Vsprayer_drone_soc.h"

// For now, use a placeholder that can be replaced when the module is available
struct DroneSoCStub {
    // Inputs
    uint8_t imuMiso = 0;
    uint8_t gpsRx = 1;
    uint8_t sbusPin = 1;
    uint8_t armSwitch = 0;
    uint8_t missionGo = 0;
    uint8_t obstacleDetect = 0;
    uint8_t batteryLow = 0;
    uint8_t clk = 0;
    uint8_t rst = 0;

    // Outputs (wire bits, will come from Verilated module)
    uint8_t dshot1 = 0, dshot2 = 0, dshot3 = 0, dshot4 = 0;
    uint8_t pump1 = 0, pump2 = 0, pump3 = 0, pump4 = 0;
    uint32_t failsafe_code = 0;

    void eval() { /* stub */ }
    void final() {}
};

static sparkle_cosim_t* shm_ptr = nullptr;
static DroneSoCStub dut;

// Decode DShot pulse stream to throttle value.
// Real implementation: track pulse widths over a full frame period.
// For v0: take the last captured throttle from an internal register.
static uint16_t decode_dshot_throttle(int motor_idx) {
    // Placeholder: in reality, you'd tap the internal _gen_throttle*
    // register via Vsprayer_drone_soc::__root_->xxx
    return 1000; // hover throttle
}

// Decode PWM duty from pulse stream (similar approach).
static uint16_t decode_pump_duty(int pump_idx) {
    return 0;
}

static bool setup_shared_memory() {
    int fd = shm_open(SPARKLE_COSIM_SHM_PATH, O_CREAT | O_RDWR, 0666);
    if (fd < 0) {
        perror("shm_open");
        return false;
    }
    if (ftruncate(fd, SPARKLE_COSIM_SHM_SIZE) < 0) {
        perror("ftruncate");
        close(fd);
        return false;
    }
    void* ptr = mmap(nullptr, SPARKLE_COSIM_SHM_SIZE,
                     PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (ptr == MAP_FAILED) {
        perror("mmap");
        return false;
    }
    shm_ptr = (sparkle_cosim_t*)ptr;

    // Initialize if first attach
    if (shm_ptr->magic != SPARKLE_COSIM_MAGIC) {
        memset(shm_ptr, 0, SPARKLE_COSIM_SHM_SIZE);
        shm_ptr->magic = SPARKLE_COSIM_MAGIC;
        shm_ptr->version = SPARKLE_COSIM_VERSION;
    }
    return true;
}

int main(int argc, char** argv) {
    if (!setup_shared_memory()) {
        fprintf(stderr, "Failed to attach shared memory\n");
        return 1;
    }

    printf("Sparkle Drone Verilator co-sim attached to %s\n", SPARKLE_COSIM_SHM_PATH);
    printf("Waiting for Gazebo to start...\n");

    // Reset SoC
    dut.rst = 1;
    for (int i = 0; i < 10; i++) {
        dut.clk = 0; dut.eval();
        dut.clk = 1; dut.eval();
    }
    dut.rst = 0;

    uint64_t total_cycles = 0;
    auto atomic_flag = [](uint32_t* p) -> std::atomic<uint32_t>* {
        return reinterpret_cast<std::atomic<uint32_t>*>(p);
    };

    while (true) {
        // ================================================================
        // Wait for Gazebo to publish sensor data
        // ================================================================
        while (atomic_flag(&shm_ptr->sensors_ready)->load(std::memory_order_acquire) == 0) {
            std::this_thread::sleep_for(std::chrono::microseconds(10));
        }

        // Read sensors from shm
        // (In a real implementation, these would drive SPI/UART/SBUS
        //  serializers connected to dut.imuMiso, dut.gpsRx, dut.sbusPin)
        // For v0, we ignore the serial protocols and directly latch values
        // into stub signals via internal register access.

        dut.obstacleDetect = shm_ptr->obstacle_detected ? 1 : 0;
        dut.batteryLow = shm_ptr->battery_low ? 1 : 0;
        dut.missionGo = 1;  // always running mission
        dut.armSwitch = 1;  // always armed

        atomic_flag(&shm_ptr->sensors_ready)->store(0, std::memory_order_release);

        // ================================================================
        // Run SoC for one control cycle (~200,000 cycles = 1 ms @ 200 MHz)
        // ================================================================
        const int cycles_per_tick = 200000;
        for (int i = 0; i < cycles_per_tick; i++) {
            dut.clk = 0; dut.eval();
            dut.clk = 1; dut.eval();
            total_cycles++;
        }

        // ================================================================
        // Write actuators to shm
        // ================================================================
        for (int m = 0; m < 4; m++) {
            shm_ptr->motor_throttle[m] = decode_dshot_throttle(m);
            shm_ptr->pump_duty[m] = decode_pump_duty(m);
        }
        shm_ptr->failsafe_code = dut.failsafe_code;
        shm_ptr->cycle_count = total_cycles;

        atomic_flag(&shm_ptr->actuators_ready)->store(1, std::memory_order_release);

        // Periodic status
        if (total_cycles % (cycles_per_tick * 1000) == 0) {
            printf("[cosim] cycles=%llu failsafe=%u\n",
                   (unsigned long long)total_cycles, shm_ptr->failsafe_code);
        }
    }

    dut.final();
    return 0;
}
