import Sparkle.Compiler.Elab
import Tests.SymbolicParameterCircuits

#synthesizeParameterizedVerilog symbolicXor [W := 8]
#synthesizeParameterizedVerilog symbolicConcat [HI := 5, LO := 3]
#synthesizeParameterizedVerilog symbolicSliceLow [W := 8]
#synthesizeParameterizedVerilog symbolicZeroExtend [W := 8]
