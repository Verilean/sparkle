import Tools.ShippingGen5RowTypedV
set_option autoImplicit false
/-! # Dependent rows on `CVEKVL` (issue sparkle-ledger-dd4-deprows; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §DepRows)

No TRUSTED, axiom, `sorry`, `native_decide`. `PT` is an arbitrary parameter; every theorem takes the row of its key as a SPEC about `PT` and the env facts as hypotheses. Existing files are unchanged.

* §1 `RowTypedAtV` of the 26 output-structure keys `Foo.mk {dom : DomainConfig} fields : Foo dom`, one theorem per key (an instance of `rowTypedAtV_depFirst`).
* §2 The evidence shape of `RowTeleEvAt` for a telescope `(dom : DC) (f₀ : Signal dom α₀) … : R` (closed payload types `αᵢ`): the first argument is the domain, the fields are `Signal` at that same domain.
  The binder type after substitution is `Signal a₀ αᵢ` (`substS` computed: `fieldsPiB_subst`, `fieldsPi_subst`), typed by the `tys` row of `Signal` and the first argument's own derivation.
* §3 One theorem per key for the 26. §4 The four named keys (`Fin.mk`, `BitVec.ofFin`, `Decidable.isTrue/isFalse`) stay named obligations with reasons. -/
namespace Tools.ShippingGen5DepRows
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV
open Tools.ShippingGen5ConstValueES (substS_liftS_in)

/-! ## §1 `RowTypedAtV`, one theorem per output-structure key -/
section rows
variable (PT : PrimTableK) (env : Environment)

/-- `Sparkle.IP.Bus.LINHW.ChkOut.mk`: `Sparkle.IP.Bus.LINHW.ChkOut dom` is typed at the first argument. -/
theorem rowTypedDep_LINHW_ChkOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Bus.LINHW.ChkOut.mk [] true ks' `Sparkle.IP.Bus.LINHW.ChkOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Bus.LINHW.ChkOut) (hT : EnvDepFirst env `Sparkle.IP.Bus.LINHW.ChkOut.mk [] ks'.length `Sparkle.IP.Bus.LINHW.ChkOut []) : RowTypedAtV PT env `Sparkle.IP.Bus.LINHW.ChkOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk`: `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut dom` is typed at the first argument. -/
theorem rowTypedDep_Keccak256HW_KeccakFOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk [] true ks' `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut) (hT : EnvDepFirst env `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk [] ks'.length `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut []) : RowTypedAtV PT env `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk`: `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut dom` is typed at the first argument. -/
theorem rowTypedDep_Keccak256Sponge_SpongeOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk [] true ks' `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut) (hT : EnvDepFirst env `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk [] ks'.length `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut []) : RowTypedAtV PT env `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk`: `Sparkle.IP.Crypto.P256FieldHW.MulOut dom` is typed at the first argument. -/
theorem rowTypedDep_P256FieldHW_MulOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk [] true ks' `Sparkle.IP.Crypto.P256FieldHW.MulOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Crypto.P256FieldHW.MulOut) (hT : EnvDepFirst env `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk [] ks'.length `Sparkle.IP.Crypto.P256FieldHW.MulOut []) : RowTypedAtV PT env `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk`: `Sparkle.IP.Crypto.P256OrderHW.MulOut dom` is typed at the first argument. -/
theorem rowTypedDep_P256OrderHW_MulOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk [] true ks' `Sparkle.IP.Crypto.P256OrderHW.MulOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Crypto.P256OrderHW.MulOut) (hT : EnvDepFirst env `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk [] ks'.length `Sparkle.IP.Crypto.P256OrderHW.MulOut []) : RowTypedAtV PT env `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk`: `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut dom` is typed at the first argument. -/
theorem rowTypedDep_Secp256k1OrderHW_MulOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk [] true ks' `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut) (hT : EnvDepFirst env `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk [] ks'.length `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut []) : RowTypedAtV PT env `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Net.HFTStrategy.HFTOut.mk`: `Sparkle.IP.Net.HFTStrategy.HFTOut dom` is typed at the first argument. -/
theorem rowTypedDep_HFTStrategy_HFTOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Net.HFTStrategy.HFTOut.mk [] true ks' `Sparkle.IP.Net.HFTStrategy.HFTOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Net.HFTStrategy.HFTOut) (hT : EnvDepFirst env `Sparkle.IP.Net.HFTStrategy.HFTOut.mk [] ks'.length `Sparkle.IP.Net.HFTStrategy.HFTOut []) : RowTypedAtV PT env `Sparkle.IP.Net.HFTStrategy.HFTOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Net.HTTP.HttpEmitOut.mk`: `Sparkle.IP.Net.HTTP.HttpEmitOut dom` is typed at the first argument. -/
theorem rowTypedDep_HTTP_HttpEmitOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Net.HTTP.HttpEmitOut.mk [] true ks' `Sparkle.IP.Net.HTTP.HttpEmitOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Net.HTTP.HttpEmitOut) (hT : EnvDepFirst env `Sparkle.IP.Net.HTTP.HttpEmitOut.mk [] ks'.length `Sparkle.IP.Net.HTTP.HttpEmitOut []) : RowTypedAtV PT env `Sparkle.IP.Net.HTTP.HttpEmitOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk`: `Sparkle.IP.Net.HTTP.HttpRequestParserOut dom` is typed at the first argument. -/
theorem rowTypedDep_HTTP_HttpRequestParserOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk [] true ks' `Sparkle.IP.Net.HTTP.HttpRequestParserOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Net.HTTP.HttpRequestParserOut) (hT : EnvDepFirst env `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk [] ks'.length `Sparkle.IP.Net.HTTP.HttpRequestParserOut []) : RowTypedAtV PT env `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.IP.Net.UART.TxOut.mk`: `Sparkle.IP.Net.UART.TxOut dom` is typed at the first argument. -/
theorem rowTypedDep_UART_TxOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.IP.Net.UART.TxOut.mk [] true ks' `Sparkle.IP.Net.UART.TxOut [])
    (hnd : ¬ IsDefn env `Sparkle.IP.Net.UART.TxOut) (hT : EnvDepFirst env `Sparkle.IP.Net.UART.TxOut.mk [] ks'.length `Sparkle.IP.Net.UART.TxOut []) : RowTypedAtV PT env `Sparkle.IP.Net.UART.TxOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk`: `Sparkle.Tests.Compiler.MultiInstance.PeOut dom` is typed at the first argument. -/
theorem rowTypedDep_MultiInstance_PeOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk [] true ks' `Sparkle.Tests.Compiler.MultiInstance.PeOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.MultiInstance.PeOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk [] ks'.length `Sparkle.Tests.Compiler.MultiInstance.PeOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk`: `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut dom` is typed at the first argument. -/
theorem rowTypedDep_NoPortsMemKidTest_KOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk [] true ks' `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk [] ks'.length `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk`: `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingChildBoundaryTest_AccOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk [] true ks' `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk`: `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingMachineEntryTest_TwoOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk [] true ks' `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk`: `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingMachineNestTest_Out (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk [] true ks' `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk`: `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingMachineNestTest_Pair (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk [] true ks' `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk`: `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingMachineSeqTest_CntOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk [] true ks' `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk`: `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingMachineTeleTest_CountOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk [] true ks' `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk`: `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut dom` is typed at the first argument. -/
theorem rowTypedDep_ShippingMachineTeleTest_PulseOut (ks' : List Bool) (hs : FirstArgSpec PT `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk [] true ks' `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut [])
    (hnd : ¬ IsDefn env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut) (hT : EnvDepFirst env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk [] ks'.length `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut []) : RowTypedAtV PT env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.KaryGenTest.KOut.mk`: `Tests.Compiler.KaryGenTest.KOut dom` is typed at the first argument. -/
theorem rowTypedDep_KaryGenTest_KOut (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.KaryGenTest.KOut.mk [] true ks' `Tests.Compiler.KaryGenTest.KOut [])
    (hnd : ¬ IsDefn env `Tests.Compiler.KaryGenTest.KOut) (hT : EnvDepFirst env `Tests.Compiler.KaryGenTest.KOut.mk [] ks'.length `Tests.Compiler.KaryGenTest.KOut []) : RowTypedAtV PT env `Tests.Compiler.KaryGenTest.KOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.KaryThreeTest.KOut.mk`: `Tests.Compiler.KaryThreeTest.KOut dom` is typed at the first argument. -/
theorem rowTypedDep_KaryThreeTest_KOut (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.KaryThreeTest.KOut.mk [] true ks' `Tests.Compiler.KaryThreeTest.KOut [])
    (hnd : ¬ IsDefn env `Tests.Compiler.KaryThreeTest.KOut) (hT : EnvDepFirst env `Tests.Compiler.KaryThreeTest.KOut.mk [] ks'.length `Tests.Compiler.KaryThreeTest.KOut []) : RowTypedAtV PT env `Tests.Compiler.KaryThreeTest.KOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk`: `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out dom` is typed at the first argument. -/
theorem rowTypedDep_SharedLeafGenDefaultHbTest_Acc16Out (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk [] true ks' `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out [])
    (hnd : ¬ IsDefn env `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out) (hT : EnvDepFirst env `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk [] ks'.length `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out []) : RowTypedAtV PT env `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk`: `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD dom` is typed at the first argument. -/
theorem rowTypedDep_SharedLeafGenDefaultHbTest_AccOutD (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk [] true ks' `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD [])
    (hnd : ¬ IsDefn env `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD) (hT : EnvDepFirst env `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk [] ks'.length `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD []) : RowTypedAtV PT env `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk`: `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF dom` is typed at the first argument. -/
theorem rowTypedDep_SharedLeafGenFallbackTest_AccOutF (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk [] true ks' `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF [])
    (hnd : ¬ IsDefn env `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF) (hT : EnvDepFirst env `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk [] ks'.length `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF []) : RowTypedAtV PT env `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk`: `Tests.Compiler.SharedLeafGenTest.Acc16Out dom` is typed at the first argument. -/
theorem rowTypedDep_SharedLeafGenTest_Acc16Out (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk [] true ks' `Tests.Compiler.SharedLeafGenTest.Acc16Out [])
    (hnd : ¬ IsDefn env `Tests.Compiler.SharedLeafGenTest.Acc16Out) (hT : EnvDepFirst env `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk [] ks'.length `Tests.Compiler.SharedLeafGenTest.Acc16Out []) : RowTypedAtV PT env `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

/-- `Tests.Compiler.SharedLeafMemKidTest.MOut.mk`: `Tests.Compiler.SharedLeafMemKidTest.MOut dom` is typed at the first argument. -/
theorem rowTypedDep_SharedLeafMemKidTest_MOut (ks' : List Bool) (hs : FirstArgSpec PT `Tests.Compiler.SharedLeafMemKidTest.MOut.mk [] true ks' `Tests.Compiler.SharedLeafMemKidTest.MOut [])
    (hnd : ¬ IsDefn env `Tests.Compiler.SharedLeafMemKidTest.MOut) (hT : EnvDepFirst env `Tests.Compiler.SharedLeafMemKidTest.MOut.mk [] ks'.length `Tests.Compiler.SharedLeafMemKidTest.MOut []) : RowTypedAtV PT env `Tests.Compiler.SharedLeafMemKidTest.MOut.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT
end rows

/-! ## §2 `RowTeleEvAt` for `(dom : DC) (f₀ : Signal dom α₀) …`

`Sig S ℓs a α` is the syntactic `Signal`-shaped binder type `S.{ℓs} a α`. -/

def Sig (S : Name) (ℓs : List Level) (a α : Expr) : Expr := .app (.app (.const S ℓs) a) α

/-- Fields as they stand in the declared type: binder `d` (counting from `k`) has type `Sig (bvar (k + d)) αd`, with closed `αd`. -/
def FieldsPiB (S : Name) (ℓs : List Level) : Expr → Nat → List Expr → Prop
  | _, _, [] => True
  | T, k, α :: αs => ∃ (x : Name) (B : Expr) (bi : BinderInfo), T = .forallE x (Sig S ℓs (.bvar k) α) B bi ∧ lbr α = 0 ∧ FieldsPiB S ℓs B (k + 1) αs

/-- Fields after the domain was substituted by `a0`: binder `d` has type `Sig (liftS a0 0 (m + d)) αd`. -/
def FieldsPi (S : Name) (ℓs : List Level) (a0 : Expr) : Expr → Nat → List Expr → Prop
  | _, _, [] => True
  | T, m, α :: αs => ∃ (x : Name) (B : Expr) (bi : BinderInfo), T = .forallE x (Sig S ℓs (liftS a0 0 m) α) B bi ∧ lbr α = 0 ∧ FieldsPi S ℓs a0 B (m + 1) αs

/-- The declared type: one binder of the constant `dc` (the domain), then the fields, then anything. -/
def DomPi (dc : Name) (S : Name) (ℓs : List Level) (T : Expr) (αs : List Expr) : Prop :=
  ∃ (x : Name) (B : Expr) (bi : BinderInfo), T = .forallE x (.const dc []) B bi ∧ FieldsPiB S ℓs B 0 αs

theorem fieldsPiB_subst (S : Name) (ℓs : List Level) (a0 : Expr) :
    ∀ (αs : List Expr) (B : Expr) (k : Nat), FieldsPiB S ℓs B k αs → FieldsPi S ℓs a0 (substS B k a0) k αs
  | [], _, _, _ => trivial
  | α :: αs, B, k, ⟨x, B', bi, hB, hα, hrest⟩ => by
    subst hB
    refine ⟨x, substS B' (k + 1) a0, bi, ?_, hα, fieldsPiB_subst S ℓs a0 αs B' (k + 1) hrest⟩
    have hc : substS α k a0 = α := substS_of_lbr_le α k a0 (by omega)
    simp [substS, Sig, hc]

theorem fieldsPi_subst (S : Name) (ℓs : List Level) (a0 f : Expr) :
    ∀ (αs : List Expr) (B : Expr) (m k : Nat), FieldsPi S ℓs a0 B m αs → k < m → FieldsPi S ℓs a0 (substS B k f) (m - 1) αs
  | [], _, _, _, _, _ => trivial
  | α :: αs, B, m, k, ⟨x, B', bi, hB, hα, hrest⟩, hk => by
    subst hB
    have hm : m - 1 + 1 = m := by omega
    refine ⟨x, substS B' (k + 1) f, bi, ?_, hα, ?_⟩
    · have hc : substS α k f = α := substS_of_lbr_le α k f (by omega)
      simp [substS, Sig, hc, substS_liftS_in a0 0 m k f (by omega) (by omega)]
    · have := fieldsPi_subst S ℓs a0 f αs B' (m + 1) (k + 1) hrest (by omega)
      rwa [show m + 1 - 1 = m - 1 + 1 by omega] at this

/-- The fields' Lean types: `SigT dv A` for the payload type `A`. -/
def ArgsAreSig {DCT : Type} (SigT : DCT → Type → Type) (dv : DCT) : List Type → List Arg → Prop
  | [], [] => True
  | A :: As, .tm d :: as => d.ty = SigT dv A ∧ ArgsAreSig SigT dv As as
  | _, _ => False

/-- The payload types denote at every valuation. -/
def AlphaDen (PT : PrimTableK) (env : Environment) : List Expr → List Type → Prop
  | [], [] => True
  | α :: αs, A :: As => (∀ ρ : Val, TDenV PT env ρ α A) ∧ AlphaDen PT env αs As
  | _, _ => False

/-- SPEC of the `tys` row of the signal type former `S ℓs` (about `PT`): a domain term and a payload type, value `SigT dv A`. -/
def SigRowSpec (PT : PrimTableK) (S : Name) (ℓs : List Level) (DCT : Type) (SigT : DCT → Type → Type) : Prop :=
  ∃ srow : TyRow, PT.tys S ℓs = some srow ∧ srow.kinds = [true, false] ∧ ∀ (dv : DCT) (A : Type), srow.den [.tm ⟨DCT, dv⟩, .ty A] = some (SigT dv A)

/-- SPEC of the `tms` row of the constructor (about `PT`): a domain value, then one value per payload type, of type `SigT dv A`. -/
def DomFieldsSpec (PT : PrimTableK) (c : Name) (ls : List Level) (DCT : Type) (SigT : DCT → Type → Type) (As : List Type) : Prop :=
  ∃ row : TmRow, PT.tms c ls = some row ∧ row.kinds = true :: List.replicate As.length true ∧
    ∀ (as : List Arg) (d : Dyn), row.den as = some d → ∃ (dv : DCT) (rest : List Arg), as = .tm ⟨DCT, dv⟩ :: rest ∧ ArgsAreSig SigT dv As rest

def EnvDomFields (env : Environment) (c : Name) (ls : List Level) (dc S : Name) (ℓs : List Level) (αs : List Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → DomPi dc S ℓs (instantiateLevelParamsS ci.levelParams ls ci.type) αs

theorem teleEv_fields (PT : PrimTableK) (env : Environment) (ρ : Val) (S : Name) (ℓs : List Level) (DCT : Type) (SigT : DCT → Type → Type)
    (hnd : ¬ IsDefn env S) (hsig : SigRowSpec PT S ℓs DCT SigT) (a0 τ0 : Expr) (dv : DCT) (hdom : CVEKV PT env ρ a0 τ0 DCT dv) :
    ∀ (αs : List Expr) (As : List Type) (T : Expr) (es : List Expr) (as : List Arg),
      FieldsPi S ℓs a0 T 0 αs → AlphaDen PT env αs As → es.length = αs.length → ArgsAreSig SigT dv As as →
      TeleEv PT env ρ T (List.replicate αs.length true) es as
  | [], As, T, es, as, _, hA, hl, hs => by
    cases As with
    | cons _ _ => exact False.elim hA
    | nil =>
      have : es = [] := List.length_eq_zero_iff.mp hl
      cases as with
      | nil => subst this; exact .nil
      | cons _ _ => exact False.elim hs
  | α :: αs, As, T, es, as, hT, hA, hl, hs => by
    obtain ⟨x, B, bi, rfl, hα, hB⟩ := hT
    cases As with
    | nil => exact False.elim hA
    | cons A As =>
      obtain ⟨hAd, hA'⟩ := hA
      cases es with
      | nil => simp at hl
      | cons e es =>
        cases as with
        | nil => exact False.elim hs
        | cons arg as =>
          cases arg with
          | ty _ => exact False.elim hs
          | tm d =>
            obtain ⟨hd, hs'⟩ := hs
            obtain ⟨srow, hsrow, hk, hden⟩ := hsig
            have hden' := hden dv A
            have hTD : TDenV PT env ρ (Sig S ℓs (liftS a0 0 0) α) d.ty := by
              rw [hd]
              have hargs : ArgsDenV PT env ρ srow.kinds [liftS a0 0 0, α] [.tm ⟨DCT, dv⟩, .ty A] := by
                rw [hk, liftS_zero]; exact .tm hdom (.ty (hAd ρ) .nil)
              exact .tcon hsrow hnd hargs hden' (by first | simp [Sig, mkAppN, mkApp] | (simp [Sig, mkAppN]; rfl))
            have hnext := fieldsPi_subst S ℓs a0 e αs B 1 0 hB (by omega)
            have ih := teleEv_fields PT env ρ S ℓs DCT SigT hnd ⟨srow, hsrow, hk, hden⟩ a0 τ0 dv hdom αs As (substS B 0 e) es as hnext hA' (by simpa using hl) hs'
            exact .tm hTD ih

/-- `RowTeleEvAt` of a `(dom : dc) (fields : Sig dom αᵢ)` constructor from: the spec of its row, the spec of the signal row, the denotation of the domain constant and of the payload types, and the env fact. -/
theorem rowTeleEvAt_domFields (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (dc S : Name) (ℓs : List Level)
    (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT c ls DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const dc []) DCT) (hAs : AlphaDen PT env αs As) (hT : EnvDomFields env c ls dc S ℓs αs) :
    RowTeleEvAt PT env c ls := by
  obtain ⟨row0, hrow0, hk, hden⟩ := hr
  have hlen : αs.length = As.length := by
    clear hT hsig hnd hdc hden hk hrow0
    induction αs generalizing As with
    | nil => cases As with | nil => rfl | cons _ _ => exact False.elim hAs
    | cons α αs ih => cases As with
      | nil => exact False.elim hAs
      | cons A As => simpa using ih As hAs.2
  intro ρ args ci row as d hci hrow hargs hd
  rw [hrow0] at hrow; cases hrow
  obtain ⟨dv, rest, has, hrest⟩ := hden as d hd
  subst has
  rw [hk] at hargs ⊢
  obtain ⟨e0, es, rfl, hhead⟩ := argsDenV_head hargs
  have hl : es.length = As.length := by have := (argsdenv_length hargs).1; simpa using this
  have hdom : ∃ τ0, CVEKV PT env ρ e0 τ0 DCT dv := by
    cases hhead with
    | tm hv _ => exact ⟨_, hv⟩
  obtain ⟨τ0, hdom⟩ := hdom
  obtain ⟨x, B, bi, hTe, hB⟩ := hT ci hci
  rw [hTe]
  have hf := fieldsPiB_subst S ℓs e0 αs B 0 hB
  have ih := teleEv_fields PT env ρ S ℓs DCT SigT hnd hsig e0 τ0 dv hdom αs As (substS B 0 e0) es rest hf hAs (by omega) hrest
  rw [← hlen]
  exact .tm (hdc ρ) ih

/-! ## §3 `RowTeleEvAt`, one theorem per output-structure key -/
section teles
variable (PT : PrimTableK) (env : Environment)

theorem teleEvDep_LINHW_ChkOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Bus.LINHW.ChkOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Bus.LINHW.ChkOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Bus.LINHW.ChkOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_Keccak256HW_KeccakFOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_Keccak256Sponge_SpongeOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_P256FieldHW_MulOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Crypto.P256FieldHW.MulOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_P256OrderHW_MulOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Crypto.P256OrderHW.MulOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_Secp256k1OrderHW_MulOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_HFTStrategy_HFTOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Net.HFTStrategy.HFTOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Net.HFTStrategy.HFTOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Net.HFTStrategy.HFTOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_HTTP_HttpEmitOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Net.HTTP.HttpEmitOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Net.HTTP.HttpEmitOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Net.HTTP.HttpEmitOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_HTTP_HttpRequestParserOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Net.HTTP.HttpRequestParserOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_UART_TxOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.IP.Net.UART.TxOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.IP.Net.UART.TxOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.IP.Net.UART.TxOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_MultiInstance_PeOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.MultiInstance.PeOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_NoPortsMemKidTest_KOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingChildBoundaryTest_AccOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingMachineEntryTest_TwoOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingMachineNestTest_Out (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingMachineNestTest_Pair (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingMachineSeqTest_CntOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingMachineTeleTest_CountOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_ShippingMachineTeleTest_PulseOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_KaryGenTest_KOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.KaryGenTest.KOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.KaryGenTest.KOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.KaryGenTest.KOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_KaryThreeTest_KOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.KaryThreeTest.KOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.KaryThreeTest.KOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.KaryThreeTest.KOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_SharedLeafGenDefaultHbTest_Acc16Out (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_SharedLeafGenDefaultHbTest_AccOutD (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_SharedLeafGenFallbackTest_AccOutF (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_SharedLeafGenTest_Acc16Out (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.SharedLeafGenTest.Acc16Out.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT

theorem teleEvDep_SharedLeafMemKidTest_MOut (S : Name) (ℓs : List Level) (αs : List Expr) (As : List Type) (DCT : Type) (SigT : DCT → Type → Type)
    (hr : DomFieldsSpec PT `Tests.Compiler.SharedLeafMemKidTest.MOut.mk [] DCT SigT As) (hsig : SigRowSpec PT S ℓs DCT SigT) (hnd : ¬ IsDefn env S)
    (hdc : ∀ ρ : Val, TDenV PT env ρ (.const `Sparkle.Core.Domain.DomainConfig []) DCT) (hAs : AlphaDen PT env αs As)
    (hT : EnvDomFields env `Tests.Compiler.SharedLeafMemKidTest.MOut.mk [] `Sparkle.Core.Domain.DomainConfig S ℓs αs) : RowTeleEvAt PT env `Tests.Compiler.SharedLeafMemKidTest.MOut.mk [] :=
  rowTeleEvAt_domFields PT env _ _ _ _ _ αs As DCT SigT hr hsig hnd hdc hAs hT
end teles

/-! ## §4 The four named keys: obligations that remain, with the reason

`RowTypedAtV` of these four is given per key below (`rowTypedDep_Fin_mk` …, instances of `rowTypedAtV_depFirst`; V2 had them as the shape theorem and one named example). Their `RowTeleEvAt` stays a NAMED obligation (a `Prop` definition, assumed nowhere):

* `Fin.mk (n val : Nat) (isLt : val < n)`: the third binder `val < n` is a proposition: it has no `Dyn` (`Arg.tm` carries `ty : Type`), so `TeleEv.tm` cannot be built from a row argument; how `PT` represents a proof argument (a kind, or no argument) is not fixed by the carrier.
* `BitVec.ofFin {w} (toFin : Fin (2 ^ w))`: the binder type `Fin (2 ^ w)` contains `HPow.hPow` with instances; typing it needs the `Fin` `tys` row AND a `CVEKV` derivation of the term `2 ^ w` (a `prim` row for `HPow.hPow`/`Nat.pow` at the argument `w`), which is `PT` content.
* `Decidable.isTrue {p : Prop} (h : p)` / `Decidable.isFalse`: the first binder is a `Prop`-valued type argument (`sort 0`), while `TeleEv.ty` ties the binder to a type argument of kind `Type`; `p` itself is not a `Type`, and `h : p` is a proof. -/

def OblTeleEv_Fin_mk (PT : PrimTableK) (env : Environment) : Prop := RowTeleEvAt PT env ``Fin.mk []
def OblTeleEv_BitVec_ofFin (PT : PrimTableK) (env : Environment) : Prop := RowTeleEvAt PT env ``BitVec.ofFin []
def OblTeleEv_Decidable_isTrue (PT : PrimTableK) (env : Environment) : Prop := RowTeleEvAt PT env ``Decidable.isTrue []
def OblTeleEv_Decidable_isFalse (PT : PrimTableK) (env : Environment) : Prop := RowTeleEvAt PT env ``Decidable.isFalse []

/- The four named dependent keys of V2 (`RowTypedAtV` per key). -/
section named
variable (PT : PrimTableK) (env : Environment)

theorem rowTypedDep_Fin_mk (ks' : List Bool) (hs : FirstArgSpec PT ``Fin.mk [] true ks' ``Fin []) (hnd : ¬ IsDefn env ``Fin)
    (hT : EnvDepFirst env ``Fin.mk [] ks'.length ``Fin []) : RowTypedAtV PT env ``Fin.mk [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

theorem rowTypedDep_BitVec_ofFin (ks' : List Bool) (hs : FirstArgSpec PT ``BitVec.ofFin [] true ks' ``BitVec []) (hnd : ¬ IsDefn env ``BitVec)
    (hT : EnvDepFirst env ``BitVec.ofFin [] ks'.length ``BitVec []) : RowTypedAtV PT env ``BitVec.ofFin [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

theorem rowTypedDep_Decidable_isTrue (ks' : List Bool) (hs : FirstArgSpec PT ``Decidable.isTrue [] true ks' ``Decidable []) (hnd : ¬ IsDefn env ``Decidable)
    (hT : EnvDepFirst env ``Decidable.isTrue [] ks'.length ``Decidable []) : RowTypedAtV PT env ``Decidable.isTrue [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

theorem rowTypedDep_Decidable_isFalse (ks' : List Bool) (hs : FirstArgSpec PT ``Decidable.isFalse [] true ks' ``Decidable []) (hnd : ¬ IsDefn env ``Decidable)
    (hT : EnvDepFirst env ``Decidable.isFalse [] ks'.length ``Decidable []) : RowTypedAtV PT env ``Decidable.isFalse [] :=
  rowTypedAtV_depFirst PT env _ _ true ks' _ _ hs hnd hT

end named

end Tools.ShippingGen5DepRows
