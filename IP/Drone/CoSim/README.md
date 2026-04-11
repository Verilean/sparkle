# Sparkle Drone Gazebo Co-Simulation

Hardware-in-the-loop-style co-simulation between Sparkle's Verilated
drone SoC and Ignition Gazebo physics.

## Architecture

```
┌──────────────┐   POSIX shared memory   ┌──────────────┐
│  Ignition    │   /sparkle_drone_cosim   │  Verilator   │
│  Gazebo      │←──────────────────────→ │  Sparkle SoC │
│              │                          │              │
│  physics     │   sensors ←─┐            │  drone SoC   │
│  rendering   │             │            │  Verilog     │
│  IMU/GPS sim │   ┌─────────┴───┐        │  (5,615 LoC) │
│  collision   │   │  handshake  │        │              │
│  motor force │   │  flags      │        │              │
│              │   └─────────────┘        │              │
│              │   actuators ──┐          │              │
│              │               │          │              │
└──────────────┘               └──────────┘──────────────┘
       ↑                                         ↓
   Gazebo plugin                          Verilator testbench
   (gazebo_plugin.cc)                     (verilator_cosim.cpp)
```

## Files

| File | Purpose |
|---|---|
| `cosim_shmem.h` | Shared memory layout (sensors + actuators), Q16.16 helpers |
| `verilator_cosim.cpp` | Verilator testbench: drives SoC from shm |
| `gazebo_plugin.cc` | Ignition Gazebo system plugin |
| `cosim_loopback_test.cpp` | Fork-based handshake test (no Gazebo/Verilator needed) |

## Handshake Protocol

Two-flag producer-consumer:

```
Gazebo                    Shared Memory              Verilator
  │                                                      │
  │ write sensors                                        │
  │ sensors_ready = 1  ─────────────────→               │
  │                                                      │ read sensors
  │                                                      │ sensors_ready = 0
  │                                                      │ run SoC tick
  │                                                      │ write actuators
  │                    ←─────────────── actuators_ready = 1
  │ read actuators                                       │
  │ actuators_ready = 0                                  │
  │ step physics                                         │
  │                                                      │
  │ (loop)                                               │
```

`std::atomic<uint32_t>` with acquire/release memory order for the flags.

## Data Format

All floating-point values are converted to Q16.16 fixed-point before
writing to shm:

```c
int32_t fixed = (int32_t)(float_value * 65536.0f);
float restored = (float)fixed / 65536.0f;
```

GPS lat/lon use 1e-7 degrees integer (matches u-blox UBX format).

## Sensor Fields (Gazebo → Verilator)

| Field | Type | Unit |
|---|---|---|
| `accel_x/y/z` | int32 Q16.16 | m/s² |
| `gyro_x/y/z` | int32 Q16.16 | rad/s |
| `gps_lat/lon` | int32 | 1e-7 deg |
| `gps_alt` | int32 Q16.16 | m |
| `gps_valid` | uint32 | flag |
| `pressure_alt` | int32 Q16.16 | m |
| `battery_voltage` | int32 Q16.16 | V |
| `battery_low` | uint32 | flag |
| `rc_ch[8]` | int16 | 172-1811 |
| `rc_failsafe` | uint32 | flag |
| `obstacle_detected` | uint32 | flag (from vision) |
| `collision` | uint32 | flag (from physics) |

## Actuator Fields (Verilator → Gazebo)

| Field | Type | Unit |
|---|---|---|
| `motor_throttle[4]` | uint16 | 48-2047 (DShot) |
| `pump_duty[4]` | uint16 | 0-65535 |
| `failsafe_code` | uint32 | 0=normal, 1-5=fault |
| `mission_done` | uint32 | flag |

## Loopback Test

Compile and run the handshake test without needing Gazebo or Verilator:

```bash
g++ -std=c++17 -O2 -I. cosim_loopback_test.cpp -o cosim_loopback -lrt
./cosim_loopback 1000     # 1000 sync cycles
./cosim_loopback 100000   # benchmark
```

Expected:
```
[verilator] Processed 100000 steps
[gazebo]    Completed 100000 steps: 100000 pass, 0 fail
=== Loopback test: gazebo=0 verilator=0 ===
```

Throughput: ~15,000 sync cycles/sec on a single x86 core. More than
enough for Gazebo physics running at 1 kHz real-time.

## Building the Real Co-Simulation

### Verilator side

```bash
# 1. Generate Verilog from Sparkle
lake env lean -e "
import IP.Drone.SprayDroneSoC
#synthesizeVerilog sprayDroneSoC
" > generated_drone_soc.sv

# 2. Verilate and build with cosim harness
verilator --cc --exe --build -j 4 -O3 \
  --top-module Sparkle_IP_Drone_sprayDroneSoC \
  -I. generated_drone_soc.sv verilator_cosim.cpp \
  -o obj_dir/sparkle_drone_cosim

# 3. Run (waits for Gazebo)
./obj_dir/sparkle_drone_cosim
```

### Gazebo plugin side

```bash
# Build against Ignition Gazebo (Fortress or Garden)
g++ -std=c++17 -fPIC -shared \
  -I$(ign gazebo --includedir) \
  gazebo_plugin.cc -o libsparkle_drone_cosim.so \
  -lignition-gazebo6 -lignition-plugin1 -lrt

# Install
cp libsparkle_drone_cosim.so ~/.ignition/gazebo/plugins/

# Reference in world SDF:
#   <plugin filename="libsparkle_drone_cosim.so"
#           name="sparkle::drone::CoSimPlugin">
#     <shm_path>/sparkle_drone_cosim</shm_path>
#   </plugin>
```

### Running both

```bash
# Terminal 1: launch Verilator
./obj_dir/sparkle_drone_cosim

# Terminal 2: launch Gazebo with the plugin-enabled world
ign gazebo spray_drone_world.sdf
```

Gazebo calls `PreUpdate` on every physics step, which writes sensors
and blocks on actuators from Verilator.

## Integration with Sparkle Drone SoC

The current `sprayDroneSoC` top module has serial I/O ports (SPI MISO,
UART RX, SBUS pin) rather than parallel register ports. For co-sim,
you have two options:

**Option A: Add a parallel I/O shim module**
Create `sprayDroneSoCParallel.lean` that wraps `sprayDroneSoC` and
exposes pre-decoded sensor values + raw actuator commands instead of
serial waveforms. This is the cleanest approach for co-sim.

**Option B: Bit-banging in verilator_cosim.cpp**
Drive the serial inputs with a software state machine that serializes
shm sensor data into SPI/UART/SBUS bit streams. More accurate (tests
the actual sensor drivers in the SoC) but slower and more complex.

Option A is recommended for initial bring-up and RL training loops.
Option B becomes valuable once you want to validate the driver
implementations with Gazebo-provided sensor noise.

### Parallel shim SoC (Option A)

Available as `sprayDroneSoCParallel` in `IP/Drone/SprayDroneSoCParallel.lean`.

Inputs/outputs (pre-decoded, parallel signals):

**Inputs**:
- 6 × IMU (accelXYZ, gyroXYZ) as `Signal dom (BitVec 32)` — Q16.16
- 3 × GPS (lat, lon, alt) as `Signal dom (BitVec 32)` — UBX format
- 5 × status flags (gpsValid, batteryLow, rcFailsafe, obstacleDetect, armSwitch, missionGo)

**Outputs**:
- 4 × motor throttle as `Signal dom (BitVec 11)` — DShot range 48-2047
- 4 × pump enable as `Signal dom Bool`
- `missionDone` + `failsafeCode : BitVec 4`

Synthesis comparison with serial version:

| Metric | Serial (SprayDroneSoC) | Parallel (SprayDroneSoCParallel) |
|---|---|---|
| Verilog lines | 5,615 | **1,810** (68% smaller) |
| Flip-flops | 216 | **33** (85% smaller) |
| LUT | ~600 | ~600 |
| DSP48 | 16 | 16 |
| Longest path | 206 | **111** |
| Ports | 10 × 1-bit | 18 (307 bits) |

The serial version's FFs were dominated by SPI/UART/SBUS/DShot FSMs.
The parallel version keeps only compute logic — Neural FC, state
estimator, path planner, failsafe, arm/obstacle mux.

For co-sim, `verilator_cosim.cpp` should be updated to drive parallel
signals directly (one shm write per sensor field → one Verilator signal
update). No bit-banging required.
