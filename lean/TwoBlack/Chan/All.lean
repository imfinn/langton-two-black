import TwoBlack.Chan.Data0
import TwoBlack.Chan.Data1
import TwoBlack.Chan.Data2
import TwoBlack.Chan.Data3
import TwoBlack.Chan.Data4
import TwoBlack.Chan.Data5
import TwoBlack.Chan.Data6
import TwoBlack.Chan.Data7
import TwoBlack.Chan.Data8
import TwoBlack.Chan.Data9
import TwoBlack.Chan.Data10
import TwoBlack.Chan.Data11
import TwoBlack.Chan.Data12
import TwoBlack.Chan.Data13
import TwoBlack.Chan.Data14
import TwoBlack.Chan.Data15
import TwoBlack.Chan.Data16
import TwoBlack.Chan.Data17
import TwoBlack.Chan.Data18
import TwoBlack.Chan.Data19
import TwoBlack.Chan.Data20
import TwoBlack.Chan.Data21

namespace TwoBlack

def chanTable : List ChanEntry := [chan0, chan1, chan2, chan3, chan4, chan5, chan6, chan7, chan8, chan9, chan10, chan11, chan12, chan13, chan14, chan15, chan16, chan17, chan18, chan19, chan20, chan21]

theorem chanTable_ok : chanTable.all (fun e => e.kids1.all Kid1.ok) = true := by
  simp only [chanTable, List.all_cons, List.all_nil, chan0_ok, chan1_ok, chan2_ok, chan3_ok, chan4_ok, chan5_ok, chan6_ok, chan7_ok, chan8_ok, chan9_ok, chan10_ok, chan11_ok, chan12_ok, chan13_ok, chan14_ok, chan15_ok, chan16_ok, chan17_ok, chan18_ok, chan19_ok, chan20_ok, chan21_ok, Bool.and_true, Bool.true_and]

end TwoBlack
