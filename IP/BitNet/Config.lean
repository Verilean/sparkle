/-
  Hespera Configuration

  Model parameters for BitNet b1.58 1B and derived constants.
  Reference: refs/hesper/Hesper/Layers/BitLinear.lean (i2_s group-128 format)
-/

namespace Sparkle.IP.BitNet

/-- BitNet b1.58 1B model parameters -/
def hiddenDim : Nat := 2048
def ffnDim    : Nat := 5632
def heads     : Nat := 32
def headDim   : Nat := 64
def layers    : Nat := 24

/-- Ternary weight packing parameters -/
def groupSize    : Nat := 128
def romWordBits  : Nat := 256   -- 128 ternary × 2 bits

/-- Fixed-point format parameters -/
def actTotalBits   : Nat := 32  -- Q16.16 signed activation
def accBits        : Nat := 48  -- 48-bit signed accumulator
def scaleTotalBits : Nat := 32  -- Q8.24 signed scale factor
def scaleFracBits  : Nat := 24  -- Fractional bits in scale
def squaredBits    : Nat := 64  -- Q16.16 × Q16.16 intermediate width
def mulProductBits : Nat := 80  -- 48-bit acc × 32-bit scale product width

/-- Attention / INT8 quantization parameters -/
def qkvBits      : Nat := 8   -- INT8 quantized activation width
def productBits  : Nat := 16  -- INT8 × INT8 signed product width
def scaleDkShift : Nat := 3   -- 1/sqrt(headDim=64) = 1/8 ≈ asr 3

/-- Softmax fixed-point parameters -/
def softmaxFracBits  : Nat := 24  -- Q8.24 attention weights
def softmaxTotalBits : Nat := 32  -- Total width of Q8.24 value
def expLutBits       : Nat := 8   -- 256-entry exp LUT index width
def recipLutBits     : Nat := 8   -- 256-entry reciprocal LUT index width

/-- Compute ceil(log2(n)), minimum 1 -/
def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else Nat.log2 (n - 1) + 1

/-- Derived constants as functions of input/output dimensions -/
def groupsPerRow (inDim : Nat) : Nat := inDim / groupSize

def romDepth (outDim inDim : Nat) : Nat := outDim * groupsPerRow inDim

def romAddrBits (outDim inDim : Nat) : Nat := ceilLog2 (romDepth outDim inDim)

def scaleDepth (outDim : Nat) : Nat := outDim

def scaleAddrBits (outDim : Nat) : Nat := ceilLog2 outDim

def actAddrBits (inDim : Nat) : Nat := ceilLog2 inDim

def groupCntBits (inDim : Nat) : Nat := ceilLog2 (groupsPerRow inDim)

/-- Configuration for a specific BitLinear layer -/
structure BitLinearConfig where
  inDim  : Nat
  outDim : Nat
  deriving Repr, BEq

namespace BitLinearConfig

def groupsPerRow (c : BitLinearConfig) : Nat := Sparkle.IP.BitNet.groupsPerRow c.inDim
def romDepth (c : BitLinearConfig) : Nat := Sparkle.IP.BitNet.romDepth c.outDim c.inDim
def romAddrBits (c : BitLinearConfig) : Nat := Sparkle.IP.BitNet.romAddrBits c.outDim c.inDim
def scaleAddrBits (c : BitLinearConfig) : Nat := Sparkle.IP.BitNet.scaleAddrBits c.outDim
def actAddrBits (c : BitLinearConfig) : Nat := Sparkle.IP.BitNet.actAddrBits c.inDim
def groupCntBits (c : BitLinearConfig) : Nat := Sparkle.IP.BitNet.groupCntBits c.inDim

end BitLinearConfig

/-- Configuration for the pipelined hardwired weight generator -/
structure GeneratorConfig where
  baseBitWidth  : Nat       -- Signed input activation width (from Hesper profiling)
  pipelineEvery : Nat       -- Insert pipeline register every N adder tree levels
  clockName     : String := "clk"
  resetName     : String := "rst"
  deriving Repr, BEq

/-- Architecture mode for SoC generation -/
inductive ArchMode where
  | HardwiredUnrolled  -- N distinct hardwired layers, no FSM, max performance
  | TimeMultiplexed    -- One generic core + weight ROM + FSM, min area
  deriving Repr, BEq, Inhabited

/-- Per-layer ternary weight data -/
structure LayerWeights where
  gateWeights : Array Int
  upWeights   : Array Int
  downWeights : Array Int
  deriving Repr, BEq, Inhabited

/-- Per-layer scale factors (Q8.24 fixed-point) -/
structure LayerScales where
  gateScale : Int
  upScale   : Int
  downScale : Int
  deriving Repr, BEq, Inhabited

/-- Configuration for the SoC top-level -/
structure SoCConfig where
  archMode      : ArchMode
  nLayers       : Nat           -- Number of transformer layers
  dim           : Nat           -- Model dimension (e.g., 4 for demo)
  ffnDim        : Nat           -- FFN intermediate dimension
  baseBitWidth  : Nat := 32     -- Activation bit width
  pipelineEvery : Nat := 0     -- Adder tree pipeline interval
  deriving Repr, BEq

/-- Standard layer configurations for BitNet b1.58 1B -/
def attnQKV : BitLinearConfig := { inDim := hiddenDim, outDim := hiddenDim }
def attnOut : BitLinearConfig := { inDim := hiddenDim, outDim := hiddenDim }
def ffnGateUp : BitLinearConfig := { inDim := hiddenDim, outDim := ffnDim }
def ffnDown : BitLinearConfig := { inDim := ffnDim, outDim := hiddenDim }

end Sparkle.IP.BitNet
