import TwoBlack.Parents.Chunk0
import TwoBlack.Parents.Chunk1
import TwoBlack.Parents.Chunk2
import TwoBlack.Parents.Chunk3
import TwoBlack.Parents.Chunk4
import TwoBlack.Parents.Chunk5
import TwoBlack.Parents.Chunk6
import TwoBlack.Parents.Chunk7
import TwoBlack.Parents.Chunk8
import TwoBlack.Parents.Chunk9
import TwoBlack.Parents.Chunk10
import TwoBlack.Parents.Chunk11
import TwoBlack.Parents.Chunk12
import TwoBlack.Parents.Chunk13
import TwoBlack.Parents.Chunk14
import TwoBlack.Parents.Chunk15
import TwoBlack.Parents.Chunk16
import TwoBlack.Parents.Chunk17
import TwoBlack.Parents.Chunk18
import TwoBlack.Parents.Chunk19
import TwoBlack.Parents.Chunk20
import TwoBlack.Parents.Chunk21
import TwoBlack.Parents.Chunk22
import TwoBlack.Parents.Chunk23
import TwoBlack.Parents.Chunk24
import TwoBlack.Parents.Chunk25
import TwoBlack.Parents.Chunk26
import TwoBlack.Parents.Chunk27
import TwoBlack.Parents.Chunk28
import TwoBlack.Parents.Chunk29
import TwoBlack.Parents.Chunk30
import TwoBlack.Parents.Chunk31

namespace TwoBlack

def parentTable : List PEntry := chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 ++ chunk17 ++ chunk18 ++ chunk19 ++ chunk20 ++ chunk21 ++ chunk22 ++ chunk23 ++ chunk24 ++ chunk25 ++ chunk26 ++ chunk27 ++ chunk28 ++ chunk29 ++ chunk30 ++ chunk31

theorem parentTable_ok : parentTable.all PEntry.ok = true := by
  simp only [parentTable, List.all_append, chunk0_ok, chunk1_ok, chunk2_ok, chunk3_ok, chunk4_ok, chunk5_ok, chunk6_ok, chunk7_ok, chunk8_ok, chunk9_ok, chunk10_ok, chunk11_ok, chunk12_ok, chunk13_ok, chunk14_ok, chunk15_ok, chunk16_ok, chunk17_ok, chunk18_ok, chunk19_ok, chunk20_ok, chunk21_ok, chunk22_ok, chunk23_ok, chunk24_ok, chunk25_ok, chunk26_ok, chunk27_ok, chunk28_ok, chunk29_ok, chunk30_ok, chunk31_ok, Bool.and_self, Bool.true_and, Bool.and_true]

end TwoBlack
