import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx2
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # The AVX2 S-box circuits' and transposition's code, as literals -/

namespace VG.Impl.TripleDes.X86_64.BitsliceAvx2

open VG.X86_64

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

def transposeProg : Prog isa := .block transpose

materialize_code transposeProg

end VG.Impl.TripleDes.X86_64.BitsliceAvx2
