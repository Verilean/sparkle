/-
  Domain Configuration for Sparkle HDL

  Defines clock domains, edge sensitivity, and reset behavior.
  Each domain has a specific clock period, active edge, and reset kind.
-/

namespace Sparkle.Core.Domain

/-- Active edge of a clock signal -/
inductive ActiveEdge where
  | rising  : ActiveEdge  -- Trigger on rising edge (0 -> 1)
  | falling : ActiveEdge  -- Trigger on falling edge (1 -> 0)
  deriving Repr, BEq, DecidableEq

/-- Reset kind: synchronous or asynchronous -/
inductive ResetKind where
  | synchronous  : ResetKind  -- Reset is synchronized with clock
  | asynchronous : ResetKind  -- Reset is asynchronous (immediate)
  deriving Repr, BEq, DecidableEq

/--
  Domain configuration specifying timing and reset behavior.

  - period: Clock period in picoseconds (e.g., 10000 for 100MHz)
  - activeEdge: Whether to trigger on rising or falling edge
  - resetKind: Synchronous or asynchronous reset
-/
structure DomainConfig where
  period      : Nat
  activeEdge  : ActiveEdge
  resetKind   : ResetKind
  deriving Repr, BEq, DecidableEq

/--
  Clock signal wrapper carrying domain information.
  The domain parameter ensures type-safe separation of different clock domains.
-/
structure Clock (dom : DomainConfig) where
  -- Clock is represented as a unit type at the type level
  -- The actual clock signal is implicit in the domain
  mk :: -- Constructor

/--
  Reset signal wrapper carrying domain information.
  Reset must belong to the same domain as the clock it synchronizes with.
-/
structure Reset (dom : DomainConfig) where
  -- Reset is represented as a unit type at the type level
  mk :: -- Constructor

/--
  Enable signal wrapper carrying domain information.
  Enable controls whether registers in a domain are active.
-/
structure Enable (dom : DomainConfig) where
  -- Enable is represented as a unit type at the type level
  mk :: -- Constructor

/-- Default domain configuration: 100MHz, rising edge, synchronous reset -/
def defaultDomain : DomainConfig :=
  { period := 10000         -- 10ns = 100MHz
  , activeEdge := .rising
  , resetKind := .synchronous
  }

/-- Common 50MHz domain -/
def domain50MHz : DomainConfig :=
  { period := 20000         -- 20ns = 50MHz
  , activeEdge := .rising
  , resetKind := .synchronous
  }

/-- Common 200MHz domain -/
def domain200MHz : DomainConfig :=
  { period := 5000          -- 5ns = 200MHz
  , activeEdge := .rising
  , resetKind := .synchronous
  }

end Sparkle.Core.Domain
