/-
  H.264 MP4 Container Muxer

  Wraps H.264 NAL units (SPS, PPS, IDR) in an ISO BMFF / MP4 container.
  Produces a playable .mp4 file from hardware pipeline output.

  Box structure (single I-frame):
    ftyp  (file type: "isom", compatible "avc1")
    moov  (movie metadata)
    ├── mvhd  (movie header)
    └── trak  (video track)
        ├── tkhd  (track header)
        └── mdia  (media)
            ├── mdhd  (media header)
            ├── hdlr  (handler: "vide")
            └── minf  (media info)
                ├── vmhd  (video media header)
                ├── dinf → dref  (data reference: self-contained)
                └── stbl  (sample table)
                    ├── stsd → avc1 → avcC  (SPS+PPS)
                    ├── stts  (time-to-sample)
                    ├── stsc  (sample-to-chunk)
                    ├── stsz  (sample sizes)
                    └── stco  (chunk offsets)
    mdat  (4-byte length prefix + IDR NAL bytes)

  Reference: ISO 14496-12 (ISOBMFF), ISO 14496-15 (AVC file format)
-/

import Sparkle

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.IP.Video.H264.MP4Mux

-- ============================================================================
-- Helpers: big-endian byte writers
-- ============================================================================

/-- Write a 32-bit value as 4 bytes, big-endian -/
def putBE32 (v : UInt32) : ByteArray :=
  let b3 := (v >>> 24).toUInt8
  let b2 := (v >>> 16).toUInt8
  let b1 := (v >>> 8).toUInt8
  let b0 := v.toUInt8
  ⟨#[b3, b2, b1, b0]⟩

/-- Write a 16-bit value as 2 bytes, big-endian -/
def putBE16 (v : UInt16) : ByteArray :=
  let b1 := (v >>> 8).toUInt8
  let b0 := v.toUInt8
  ⟨#[b1, b0]⟩

/-- Write a string as raw bytes (no null terminator) -/
def putStr (s : String) : ByteArray :=
  s.toUTF8

/-- Zero-filled ByteArray of given length -/
def zeros (n : Nat) : ByteArray :=
  ⟨Array.replicate n 0⟩

-- ============================================================================
-- Generic MP4 box
-- ============================================================================

/-- Build an MP4 box: [size:4][type:4][payload] -/
def mp4Box (boxType : String) (payload : ByteArray) : ByteArray :=
  let size := (8 + payload.size).toUInt32
  putBE32 size ++ putStr boxType ++ payload

-- ============================================================================
-- File Type Box (ftyp)
-- ============================================================================

/-- ftyp box: "isom" brand, compatible with "isom" and "avc1" -/
def buildFtyp : ByteArray :=
  mp4Box "ftyp" (
    putStr "isom" ++       -- major_brand
    putBE32 0x200 ++       -- minor_version
    putStr "isom" ++       -- compatible_brand[0]
    putStr "avc1"          -- compatible_brand[1]
  )

-- ============================================================================
-- Movie Header Box (mvhd) — version 0
-- ============================================================================

/-- mvhd box: movie header (version 0, 108 bytes total) -/
def buildMvhd (timescale duration : UInt32) : ByteArray :=
  mp4Box "mvhd" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 0 ++           -- creation_time
    putBE32 0 ++           -- modification_time
    putBE32 timescale ++   -- timescale
    putBE32 duration ++    -- duration
    putBE32 0x00010000 ++  -- rate = 1.0 (fixed point 16.16)
    putBE16 0x0100 ++      -- volume = 1.0 (fixed point 8.8)
    zeros 10 ++            -- reserved
    -- unity matrix (9 × 4 bytes = 36 bytes)
    putBE32 0x00010000 ++ putBE32 0 ++ putBE32 0 ++
    putBE32 0 ++ putBE32 0x00010000 ++ putBE32 0 ++
    putBE32 0 ++ putBE32 0 ++ putBE32 0x40000000 ++
    zeros 24 ++            -- pre_defined (6 × 4 bytes)
    putBE32 2              -- next_track_ID
  )

-- ============================================================================
-- Track Header Box (tkhd) — version 0
-- ============================================================================

/-- tkhd box: track header (version 0, 92 bytes total) -/
def buildTkhd (width height : UInt16) (dur : UInt32) : ByteArray :=
  mp4Box "tkhd" (
    putBE32 0x00000003 ++  -- version(0) + flags(track_enabled | track_in_movie)
    putBE32 0 ++           -- creation_time
    putBE32 0 ++           -- modification_time
    putBE32 1 ++           -- track_ID
    putBE32 0 ++           -- reserved
    putBE32 dur ++         -- duration
    zeros 8 ++             -- reserved
    putBE16 0 ++           -- layer
    putBE16 0 ++           -- alternate_group
    putBE16 0 ++           -- volume (0 for video)
    putBE16 0 ++           -- reserved
    -- unity matrix (9 × 4 bytes)
    putBE32 0x00010000 ++ putBE32 0 ++ putBE32 0 ++
    putBE32 0 ++ putBE32 0x00010000 ++ putBE32 0 ++
    putBE32 0 ++ putBE32 0 ++ putBE32 0x40000000 ++
    -- width/height in 16.16 fixed point
    putBE32 (width.toUInt32 <<< 16) ++
    putBE32 (height.toUInt32 <<< 16)
  )

-- ============================================================================
-- Media Header Box (mdhd) — version 0
-- ============================================================================

/-- mdhd box: media header -/
def buildMdhd (timescale duration : UInt32) : ByteArray :=
  mp4Box "mdhd" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 0 ++           -- creation_time
    putBE32 0 ++           -- modification_time
    putBE32 timescale ++   -- timescale
    putBE32 duration ++    -- duration
    putBE16 0x55C4 ++      -- language = "und" (packed ISO 639-2/T)
    putBE16 0              -- pre_defined
  )

-- ============================================================================
-- Handler Reference Box (hdlr)
-- ============================================================================

/-- hdlr box: video handler -/
def buildHdlr : ByteArray :=
  mp4Box "hdlr" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 0 ++           -- pre_defined
    putStr "vide" ++       -- handler_type
    zeros 12 ++            -- reserved (3 × 4 bytes)
    putStr "VideoHandler" ++ ⟨#[0]⟩  -- name (null-terminated)
  )

-- ============================================================================
-- Video Media Header Box (vmhd)
-- ============================================================================

/-- vmhd box: video media header -/
def buildVmhd : ByteArray :=
  mp4Box "vmhd" (
    putBE32 0x00000001 ++  -- version(0) + flags(1)
    putBE16 0 ++           -- graphicsmode
    zeros 6                -- opcolor (3 × 2 bytes)
  )

-- ============================================================================
-- Data Information Box (dinf → dref)
-- ============================================================================

/-- dinf box containing a dref with one self-contained entry -/
def buildDinf : ByteArray :=
  let dref := mp4Box "dref" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 1 ++           -- entry_count
    mp4Box "url " (
      putBE32 0x00000001   -- version(0) + flags(self-contained = 1)
    )
  )
  mp4Box "dinf" dref

-- ============================================================================
-- Sample Table Boxes (stbl components)
-- ============================================================================

/-- stts box: time-to-sample (1 entry) -/
def buildStts (count delta : UInt32) : ByteArray :=
  mp4Box "stts" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 1 ++           -- entry_count
    putBE32 count ++       -- sample_count
    putBE32 delta          -- sample_delta
  )

/-- stsc box: sample-to-chunk (1 entry: all in chunk 1) -/
def buildStsc : ByteArray :=
  mp4Box "stsc" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 1 ++           -- entry_count
    putBE32 1 ++           -- first_chunk
    putBE32 1 ++           -- samples_per_chunk
    putBE32 1              -- sample_description_index
  )

/-- stsz box: sample sizes -/
def buildStsz (sizes : Array UInt32) : ByteArray := Id.run do
  let mut payload := putBE32 0    -- version(0) + flags(0)
  payload := payload ++ putBE32 0 -- sample_size = 0 (variable)
  payload := payload ++ putBE32 sizes.size.toUInt32 -- sample_count
  for sz in sizes do
    payload := payload ++ putBE32 sz
  mp4Box "stsz" payload

/-- stco box: chunk offsets (32-bit) -/
def buildStco (offsets : Array UInt32) : ByteArray := Id.run do
  let mut payload := putBE32 0    -- version(0) + flags(0)
  payload := payload ++ putBE32 offsets.size.toUInt32 -- entry_count
  for off in offsets do
    payload := payload ++ putBE32 off
  mp4Box "stco" payload

-- ============================================================================
-- H.264 Specific: avcC (AVC Decoder Configuration Record)
-- ============================================================================

/-- Build avcC box (AVC Decoder Configuration Record).
    sps/pps: NAL unit bytes WITHOUT start code prefix.
    E.g., sps starts with 0x67 (NAL header), pps starts with 0x68. -/
def buildAvcC (sps pps : ByteArray) : ByteArray :=
  mp4Box "avcC" (
    ⟨#[
      1,                           -- configurationVersion
      sps.data[1]!,                -- AVCProfileIndication (0x42 = Baseline)
      sps.data[2]!,                -- profile_compatibility (0xC0)
      sps.data[3]!,                -- AVCLevelIndication (0x0A)
      0xFF                         -- lengthSizeMinusOne = 3 (0b111111_11)
    ]⟩ ++
    -- SPS
    ⟨#[0xE1]⟩ ++                   -- numOfSequenceParameterSets = 1 (0b111_00001)
    putBE16 sps.size.toUInt16 ++
    sps ++
    -- PPS
    ⟨#[0x01]⟩ ++                   -- numOfPictureParameterSets = 1
    putBE16 pps.size.toUInt16 ++
    pps
  )

-- ============================================================================
-- Sample Description Box (stsd → avc1 → avcC)
-- ============================================================================

/-- Build stsd box containing an avc1 sample entry -/
def buildStsd (w h : UInt16) (sps pps : ByteArray) : ByteArray :=
  let avcC := buildAvcC sps pps
  let avc1 := mp4Box "avc1" (
    zeros 6 ++             -- reserved
    putBE16 1 ++           -- data_reference_index
    putBE16 0 ++           -- pre_defined
    putBE16 0 ++           -- reserved
    zeros 12 ++            -- pre_defined (3 × 4 bytes)
    putBE16 w ++           -- width
    putBE16 h ++           -- height
    putBE32 0x00480000 ++  -- horizresolution = 72 dpi (16.16)
    putBE32 0x00480000 ++  -- vertresolution = 72 dpi (16.16)
    putBE32 0 ++           -- reserved
    putBE16 1 ++           -- frame_count
    zeros 32 ++            -- compressorname (32 bytes)
    putBE16 0x0018 ++      -- depth = 24
    putBE16 0xFFFF ++      -- pre_defined = -1
    avcC
  )
  mp4Box "stsd" (
    putBE32 0 ++           -- version(0) + flags(0)
    putBE32 1 ++           -- entry_count
    avc1
  )

-- ============================================================================
-- Top-level: mux a single IDR frame into MP4
-- ============================================================================

/-- Mux a single H.264 IDR frame into an MP4 container.
    - sps: SPS NAL unit bytes WITHOUT start code (starts with 0x67)
    - pps: PPS NAL unit bytes WITHOUT start code (starts with 0x68)
    - idr: IDR NAL unit bytes WITHOUT start code (starts with 0x65)
    - width, height: frame dimensions in pixels
    - fps: frames per second (default 25) -/
def muxSingleFrame (sps pps idr : ByteArray)
    (width height : UInt16) (fps : UInt32 := 25) : ByteArray :=
  let timescale : UInt32 := 600
  let frameDuration : UInt32 := timescale / fps  -- e.g., 600/25 = 24

  -- mdat content: 4-byte big-endian length prefix + IDR NAL bytes
  let mdatPayload := putBE32 idr.size.toUInt32 ++ idr
  let mdat := mp4Box "mdat" mdatPayload

  -- IDR sample size = 4-byte length + IDR NAL bytes
  let sampleSize := (4 + idr.size).toUInt32

  -- Build ftyp (fixed size)
  let ftyp := buildFtyp

  -- Build stbl components (all except stco, which needs the final offset)
  let stsd := buildStsd width height sps pps
  let stts := buildStts 1 frameDuration
  let stsc := buildStsc
  let stsz := buildStsz #[sampleSize]

  -- To compute stco, we need to know ftyp.size + moov.size + mdat_header(8).
  -- But moov.size depends on stco.size. Since stco has a fixed structure
  -- (1 entry = 20 bytes total box), we can compute moov size with a placeholder.
  let stcoPlaceholder := buildStco #[0]

  let stbl := mp4Box "stbl" (stsd ++ stts ++ stsc ++ stsz ++ stcoPlaceholder)
  let minf := mp4Box "minf" (buildVmhd ++ buildDinf ++ stbl)
  let mdia := mp4Box "mdia" (buildMdhd timescale frameDuration ++ buildHdlr ++ minf)
  let trak := mp4Box "trak" (buildTkhd width height frameDuration ++ mdia)
  let moov := mp4Box "moov" (buildMvhd timescale frameDuration ++ trak)

  -- Chunk offset = ftyp.size + moov.size + mdat_box_header(8)
  let chunkOffset := (ftyp.size + moov.size + 8).toUInt32

  -- Rebuild with correct stco offset
  let stco := buildStco #[chunkOffset]
  let stbl := mp4Box "stbl" (stsd ++ stts ++ stsc ++ stsz ++ stco)
  let minf := mp4Box "minf" (buildVmhd ++ buildDinf ++ stbl)
  let mdia := mp4Box "mdia" (buildMdhd timescale frameDuration ++ buildHdlr ++ minf)
  let trak := mp4Box "trak" (buildTkhd width height frameDuration ++ mdia)
  let moov := mp4Box "moov" (buildMvhd timescale frameDuration ++ trak)

  ftyp ++ moov ++ mdat

-- ============================================================================
-- MP4 ROM Template for Hardware Muxer
-- ============================================================================

/-- Build 629-byte ftyp+moov ROM template with placeholder width=16, height=16.
    The hardware muxer patches width/height/stsz at runtime.

    Patch offsets (byte index within ROM):
    - 232–235: tkhd width  (BE32, width << 16)
    - 236–239: tkhd height (BE32, height << 16)
    - 445–446: avc1 width  (BE16)
    - 447–448: avc1 height (BE16)
    - 605–608: stsz entry  (BE32, 4 + idrNalSize)
    - 625–628: stco entry  (BE32, always 637) -/
def buildMP4ROMTemplate : Array UInt8 :=
  -- Build a template using placeholder IDR (1 byte) so stsz/stco get real structure
  let sps : ByteArray := ⟨#[0x67, 0x42, 0xC0, 0x0A, 0x8C, 0x69, 0xC8, 0x07, 0x84, 0x42, 0x35]⟩
  let pps : ByteArray := ⟨#[0x68, 0xCE, 0x3C, 0x80]⟩
  let placeholderIdr : ByteArray := ⟨#[0x65]⟩  -- minimal 1-byte IDR placeholder
  let mp4 := muxSingleFrame sps pps placeholderIdr 16 16
  -- Extract just ftyp + moov (first 629 bytes, skip mdat)
  let romSize := mp4.size - 13  -- subtract mdat box (8 header + 4 length + 1 IDR)
  Id.run do
    let mut arr : Array UInt8 := #[]
    for i in [:romSize] do
      if h : i < mp4.size then
        arr := arr.push mp4.data[i]
    arr

end Sparkle.IP.Video.H264.MP4Mux
