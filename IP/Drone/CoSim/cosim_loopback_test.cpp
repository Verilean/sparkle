// Loopback test: two processes attach to the same shm, one plays
// Gazebo (writes sensors, reads actuators), the other plays Verilator
// (reads sensors, writes actuators). Verifies handshake + data
// roundtrip without needing either real software.
//
// Run: ./cosim_loopback_test         (spawns both roles via fork)

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

static sparkle_cosim_t* attach_shm() {
    int fd = shm_open(SPARKLE_COSIM_SHM_PATH, O_CREAT | O_RDWR, 0666);
    if (fd < 0) { perror("shm_open"); return nullptr; }
    if (ftruncate(fd, SPARKLE_COSIM_SHM_SIZE) < 0) {
        perror("ftruncate"); close(fd); return nullptr;
    }
    void* ptr = mmap(nullptr, SPARKLE_COSIM_SHM_SIZE,
                     PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (ptr == MAP_FAILED) { perror("mmap"); return nullptr; }
    return (sparkle_cosim_t*)ptr;
}

static auto flag(uint32_t* p) {
    return reinterpret_cast<std::atomic<uint32_t>*>(p);
}

static int run_gazebo_role(int n_steps) {
    auto* shm = attach_shm();
    if (!shm) return 1;

    if (shm->magic != SPARKLE_COSIM_MAGIC) {
        memset(shm, 0, SPARKLE_COSIM_SHM_SIZE);
        shm->magic = SPARKLE_COSIM_MAGIC;
        shm->version = SPARKLE_COSIM_VERSION;
    }

    uint16_t expected_throttle[4] = {0, 0, 0, 0};
    int passes = 0, fails = 0;

    for (int step = 0; step < n_steps; step++) {
        // Write sensor data (varies by step for verification)
        shm->accel_x = cosim_f2q((float)step * 0.1f);
        shm->accel_y = cosim_f2q(0.0f);
        shm->accel_z = cosim_f2q(-9.81f);
        shm->gyro_x = cosim_f2q(0.0f);
        shm->gyro_y = cosim_f2q(0.0f);
        shm->gyro_z = cosim_f2q(0.0f);
        shm->gps_lat = 356895000 + step;
        shm->gps_lon = 1396917000;
        shm->gps_alt = cosim_f2q(100.0f);
        shm->gps_valid = 1;
        shm->battery_voltage = cosim_f2q(12.6f);
        shm->obstacle_detected = (step % 5 == 0) ? 1 : 0;

        // Expected: Verilator echoes back step as throttle value
        expected_throttle[0] = (uint16_t)(step & 0xFFFF);

        flag(&shm->actuators_ready)->store(0, std::memory_order_release);
        flag(&shm->sensors_ready)->store(1, std::memory_order_release);

        // Wait for actuators
        auto start = std::chrono::steady_clock::now();
        while (flag(&shm->actuators_ready)->load(std::memory_order_acquire) == 0) {
            if (std::chrono::steady_clock::now() - start > std::chrono::seconds(5)) {
                fprintf(stderr, "[gazebo] timeout waiting for verilator\n");
                return 2;
            }
            std::this_thread::sleep_for(std::chrono::microseconds(10));
        }

        // Verify roundtrip
        if (shm->motor_throttle[0] == expected_throttle[0]) passes++;
        else {
            fails++;
            if (fails < 5) {
                fprintf(stderr, "[gazebo] step %d: got %u, expected %u\n",
                        step, shm->motor_throttle[0], expected_throttle[0]);
            }
        }
    }

    printf("[gazebo] Completed %d steps: %d pass, %d fail\n", n_steps, passes, fails);
    munmap(shm, SPARKLE_COSIM_SHM_SIZE);
    return fails == 0 ? 0 : 1;
}

static int run_verilator_role(int n_steps) {
    auto* shm = attach_shm();
    if (!shm) return 1;

    // Wait for gazebo to initialize shm
    while (shm->magic != SPARKLE_COSIM_MAGIC) {
        std::this_thread::sleep_for(std::chrono::microseconds(100));
    }

    int processed = 0;

    for (int step = 0; step < n_steps; step++) {
        // Wait for sensors
        auto start = std::chrono::steady_clock::now();
        while (flag(&shm->sensors_ready)->load(std::memory_order_acquire) == 0) {
            if (std::chrono::steady_clock::now() - start > std::chrono::seconds(5)) {
                fprintf(stderr, "[verilator] timeout waiting for gazebo\n");
                return 2;
            }
            std::this_thread::sleep_for(std::chrono::microseconds(10));
        }

        // Read sensors (verify format)
        float ax = cosim_q2f(shm->accel_x);
        // Echo step back as motor throttle (simulates SoC output)
        shm->motor_throttle[0] = (uint16_t)(step & 0xFFFF);
        shm->motor_throttle[1] = 1000;
        shm->motor_throttle[2] = 1000;
        shm->motor_throttle[3] = 1000;
        shm->failsafe_code = shm->obstacle_detected ? 4 : 0;
        shm->cycle_count = step * 200000;

        (void)ax;

        flag(&shm->sensors_ready)->store(0, std::memory_order_release);
        flag(&shm->actuators_ready)->store(1, std::memory_order_release);
        processed++;
    }

    printf("[verilator] Processed %d steps\n", processed);
    munmap(shm, SPARKLE_COSIM_SHM_SIZE);
    return 0;
}

int main(int argc, char** argv) {
    // Clean up any stale shm
    shm_unlink(SPARKLE_COSIM_SHM_PATH);

    int n_steps = 100;
    if (argc > 1) n_steps = atoi(argv[1]);

    pid_t gz = fork();
    if (gz == 0) return run_gazebo_role(n_steps);

    // Brief delay so gazebo initializes shm first
    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    pid_t vl = fork();
    if (vl == 0) return run_verilator_role(n_steps);

    int gz_status, vl_status;
    waitpid(gz, &gz_status, 0);
    waitpid(vl, &vl_status, 0);

    shm_unlink(SPARKLE_COSIM_SHM_PATH);

    int gz_ret = WEXITSTATUS(gz_status);
    int vl_ret = WEXITSTATUS(vl_status);

    printf("\n=== Loopback test: gazebo=%d verilator=%d ===\n", gz_ret, vl_ret);
    return (gz_ret == 0 && vl_ret == 0) ? 0 : 1;
}
