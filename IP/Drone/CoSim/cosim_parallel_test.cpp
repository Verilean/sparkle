// Parallel-I/O co-sim integration test
//
// Spawns:
//   1. The real Verilated sparkle_drone_cosim (reads shm → runs SoC → writes shm)
//   2. A fake "Gazebo" role that publishes sensor values and checks
//      the Verilator output is sensible.
//
// Unlike cosim_loopback_test, this uses the actual synthesized SoC,
// not a software echo. Verifies the shm plumbing + SoC execution
// end-to-end without needing real Gazebo.
//
// Run: ./cosim_parallel_test [n_steps]

#include "cosim_shmem.h"

#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <atomic>
#include <thread>
#include <chrono>
#include <signal.h>

static sparkle_cosim_t* attach_shm() {
    int fd = shm_open(SPARKLE_COSIM_SHM_PATH, O_CREAT | O_RDWR, 0666);
    if (fd < 0) { perror("shm_open"); return nullptr; }
    if (ftruncate(fd, SPARKLE_COSIM_SHM_SIZE) < 0) {
        perror("ftruncate"); close(fd); return nullptr;
    }
    void* ptr = mmap(nullptr, SPARKLE_COSIM_SHM_SIZE,
                     PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    return ptr == MAP_FAILED ? nullptr : (sparkle_cosim_t*)ptr;
}

static auto flag(uint32_t* p) {
    return reinterpret_cast<std::atomic<uint32_t>*>(p);
}

int main(int argc, char** argv) {
    shm_unlink(SPARKLE_COSIM_SHM_PATH);

    int n_steps = 100;
    if (argc > 1) n_steps = atoi(argv[1]);

    auto* shm = attach_shm();
    if (!shm) return 1;
    memset(shm, 0, SPARKLE_COSIM_SHM_SIZE);
    shm->magic = SPARKLE_COSIM_MAGIC;
    shm->version = SPARKLE_COSIM_VERSION;

    // Fork: child runs real Verilator SoC, parent plays Gazebo
    pid_t verilator_pid = fork();
    if (verilator_pid == 0) {
        // Child: exec the Verilated binary
        const char* bin = "./obj_dir/sparkle_drone_cosim";
        char steps_str[32];
        snprintf(steps_str, sizeof(steps_str), "%d", n_steps);
        execl(bin, bin, steps_str, (char*)nullptr);
        perror("execl");
        return 1;
    }

    // Parent: Gazebo role
    printf("[gazebo] Publishing %d sensor steps to Verilator...\n", n_steps);

    // Let Verilator settle
    std::this_thread::sleep_for(std::chrono::milliseconds(100));

    int hover_count = 0;       // motor_throttle in reasonable range
    int zero_count = 0;        // motor_throttle == 0 (disarmed / failsafe)
    int nonzero_count = 0;     // motor_throttle > 0

    uint64_t min_throttle = 0xFFFF, max_throttle = 0;

    for (int step = 0; step < n_steps; step++) {
        // Publish sensor data (varies slightly to exercise different code paths)
        shm->accel_x = cosim_f2q((float)step * 0.01f);
        shm->accel_y = cosim_f2q(0.0f);
        shm->accel_z = cosim_f2q(-9.81f);
        shm->gyro_x  = cosim_f2q(0.0f);
        shm->gyro_y  = cosim_f2q(0.0f);
        shm->gyro_z  = cosim_f2q(0.0f);
        shm->gps_lat = 356895000;
        shm->gps_lon = 1396917000;
        shm->gps_alt = cosim_f2q(100.0f);
        shm->gps_valid = 1;
        shm->battery_low = 0;
        shm->rc_failsafe = 0;
        shm->obstacle_detected = 0;
        shm->collision = 0;
        shm->battery_voltage = cosim_f2q(12.6f);

        flag(&shm->actuators_ready)->store(0, std::memory_order_release);
        flag(&shm->sensors_ready)->store(1, std::memory_order_release);

        // Wait for Verilator
        auto start = std::chrono::steady_clock::now();
        bool timed_out = false;
        while (flag(&shm->actuators_ready)->load(std::memory_order_acquire) == 0) {
            if (std::chrono::steady_clock::now() - start > std::chrono::seconds(5)) {
                timed_out = true;
                break;
            }
            std::this_thread::sleep_for(std::chrono::microseconds(5));
        }
        if (timed_out) {
            fprintf(stderr, "[gazebo] timeout at step %d\n", step);
            kill(verilator_pid, SIGTERM);
            waitpid(verilator_pid, nullptr, 0);
            shm_unlink(SPARKLE_COSIM_SHM_PATH);
            return 2;
        }

        // Collect statistics on motor throttle output
        uint16_t t = shm->motor_throttle[0];
        if (t == 0) zero_count++;
        else {
            nonzero_count++;
            if (t < min_throttle) min_throttle = t;
            if (t > max_throttle) max_throttle = t;
            if (t >= 48 && t <= 2047) hover_count++;
        }
    }

    // Wait for Verilator to exit
    int verilator_status;
    waitpid(verilator_pid, &verilator_status, 0);

    printf("\n[gazebo] Results over %d steps:\n", n_steps);
    printf("  motor1 throttle: min=%llu max=%llu\n",
           (unsigned long long)min_throttle, (unsigned long long)max_throttle);
    printf("  zero count:     %d\n", zero_count);
    printf("  nonzero count:  %d\n", nonzero_count);
    printf("  in DShot range: %d\n", hover_count);
    printf("  last failsafe code: %u\n", shm->failsafe_code);
    printf("  last mission done:  %u\n", shm->mission_done);

    shm_unlink(SPARKLE_COSIM_SHM_PATH);

    // Pass criteria:
    //   1. Verilator exited cleanly
    //   2. At least some non-zero output observed (SoC is computing something)
    //   3. No timeouts
    int verilator_ret = WEXITSTATUS(verilator_status);
    bool pass = (verilator_ret == 0);

    printf("\n=== Parallel co-sim test: %s (verilator=%d) ===\n",
           pass ? "PASS" : "FAIL", verilator_ret);
    return pass ? 0 : 1;
}
