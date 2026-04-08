/-
  YOLOv8n-WorldV2 Configuration

  Model parameters for YOLOv8n-WorldV2 with INT4 weight / INT8 activation quantization.
  Input: 160x160x3 RGB image.
-/

namespace Sparkle.IP.YOLOv8

-- ============================================================================
-- Input Image Parameters
-- ============================================================================

def imageWidth  : Nat := 160
def imageHeight : Nat := 160
def imageChannels : Nat := 3

-- ============================================================================
-- Backbone Channel Widths (YOLOv8n: 0.25 width multiplier)
-- ============================================================================

/-- Stem output channels -/
def stemChannels : Nat := 16

/-- Stage 1 output channels -/
def stage1Channels : Nat := 32

/-- Stage 2 output channels (P3 feature map) -/
def stage2Channels : Nat := 64

/-- Stage 3 output channels (P4 feature map) -/
def stage3Channels : Nat := 128

/-- Stage 4 output channels (P5 feature map) -/
def stage4Channels : Nat := 256

-- ============================================================================
-- C2f Block Depths (number of Bottleneck blocks per C2f)
-- ============================================================================

def c2fDepth1 : Nat := 1  -- Stage 1
def c2fDepth2 : Nat := 2  -- Stage 2
def c2fDepth3 : Nat := 2  -- Stage 3
def c2fDepth4 : Nat := 1  -- Stage 4

-- ============================================================================
-- Convolution Parameters
-- ============================================================================

def kernelSize3x3 : Nat := 3
def kernelSize1x1 : Nat := 1
def stride1 : Nat := 1
def stride2 : Nat := 2
def padding1 : Nat := 1  -- padding for 3x3 conv
def padding0 : Nat := 0  -- padding for 1x1 conv

-- ============================================================================
-- Detection Head Parameters
-- ============================================================================

/-- Number of regression outputs per anchor: 4 * (reg_max + 1) -/
def regMax : Nat := 16
def bboxOutputs : Nat := 4 * (regMax + 1)  -- = 68

/-- Feature map sizes at each scale (after stride) -/
def fmapSize_P3 : Nat := imageWidth / 8   -- = 20
def fmapSize_P4 : Nat := imageWidth / 16  -- = 10
def fmapSize_P5 : Nat := imageWidth / 32  -- = 5

-- ============================================================================
-- Quantization Parameters
-- ============================================================================

/-- Weight bit width (INT4, packed 2 per byte) -/
def weightBits : Nat := 4

/-- Activation bit width (INT8) -/
def activationBits : Nat := 8

/-- Accumulator bit width (INT32) -/
def accumulatorBits : Nat := 32

/-- Requantization scale bit width -/
def scaleBits : Nat := 16

/-- Requantization shift bit width -/
def shiftBits : Nat := 5

/-- Max shift value for requantization -/
def maxShift : Nat := 31

-- ============================================================================
-- SiLU LUT Parameters
-- ============================================================================

/-- Number of entries in the sigmoid lookup table -/
def siluLutSize : Nat := 256

/-- Address width for SiLU LUT -/
def siluLutAddrBits : Nat := 8

-- ============================================================================
-- SPPF Parameters
-- ============================================================================

/-- SPPF max-pool kernel size -/
def sppfPoolSize : Nat := 5

/-- Number of sequential max-pool stages in SPPF -/
def sppfPoolStages : Nat := 3

-- ============================================================================
-- Text Embedding Parameters
-- ============================================================================

/-- CLIP text embedding dimension -/
def textEmbedDim : Nat := 512

/-- Maximum number of text prompts (classes) -/
def maxClasses : Nat := 80

-- ============================================================================
-- Utility Functions
-- ============================================================================

/-- Compute ceil(log2(n)), minimum 1 -/
def ceilLog2 (n : Nat) : Nat :=
  if n <= 1 then 1
  else Nat.log2 (n - 1) + 1

/-- Address width needed for a memory of given depth -/
def addrWidth (depth : Nat) : Nat := ceilLog2 depth

/-- Number of MAC operations for a single output pixel of a conv layer -/
def convMacOps (kernelH kernelW inChannels : Nat) : Nat :=
  kernelH * kernelW * inChannels

/-- Configuration for a convolutional layer -/
structure ConvConfig where
  inChannels  : Nat
  outChannels : Nat
  kernelSize  : Nat
  stride      : Nat
  padding     : Nat
  deriving Repr, BEq

/-- Configuration for the overall YOLOv8n model -/
structure YoloConfig where
  imgW         : Nat := imageWidth
  imgH         : Nat := imageHeight
  stemCh       : Nat := stemChannels
  s1Ch         : Nat := stage1Channels
  s2Ch         : Nat := stage2Channels
  s3Ch         : Nat := stage3Channels
  s4Ch         : Nat := stage4Channels
  c2fD1        : Nat := c2fDepth1
  c2fD2        : Nat := c2fDepth2
  c2fD3        : Nat := c2fDepth3
  c2fD4        : Nat := c2fDepth4
  deriving Repr, BEq

/-- Default configuration for YOLOv8n -/
def defaultConfig : YoloConfig := {}

end Sparkle.IP.YOLOv8
