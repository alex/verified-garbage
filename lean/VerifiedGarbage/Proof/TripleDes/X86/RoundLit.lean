import VerifiedGarbage.Proof.TripleDes.X86.SboxTable
import VerifiedGarbage.Impl.TripleDes.X86.Block
import VerifiedGarbage.Proof.Framework.X86.Lit
namespace VG.Impl.TripleDes.X86
open VG.X86
def input0 : Prog isa := .block (sboxInputBits 0)
materialize_code input0
def output0 : Prog isa := .block (sboxOutputs 0)
materialize_code output0
def input1 : Prog isa := .block (sboxInputBits 1)
materialize_code input1
def output1 : Prog isa := .block (sboxOutputs 1)
materialize_code output1
def input2 : Prog isa := .block (sboxInputBits 2)
materialize_code input2
def output2 : Prog isa := .block (sboxOutputs 2)
materialize_code output2
def input3 : Prog isa := .block (sboxInputBits 3)
materialize_code input3
def output3 : Prog isa := .block (sboxOutputs 3)
materialize_code output3
def input4 : Prog isa := .block (sboxInputBits 4)
materialize_code input4
def output4 : Prog isa := .block (sboxOutputs 4)
materialize_code output4
def input5 : Prog isa := .block (sboxInputBits 5)
materialize_code input5
def output5 : Prog isa := .block (sboxOutputs 5)
materialize_code output5
def input6 : Prog isa := .block (sboxInputBits 6)
materialize_code input6
def output6 : Prog isa := .block (sboxOutputs 6)
materialize_code output6
def input7 : Prog isa := .block (sboxInputBits 7)
materialize_code input7
def output7 : Prog isa := .block (sboxOutputs 7)
materialize_code output7
end VG.Impl.TripleDes.X86
