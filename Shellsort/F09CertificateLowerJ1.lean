import Shellsort.F09CertificateLowerJ1A
import Shellsort.F09CertificateLowerJ1B
import Shellsort.F09CertificateLowerJ1C
import Shellsort.F09CertificateLowerJ1D

namespace Shellsort.F09.Quad.LowerJ1
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 55136638157, 67104378014, 76994936469, 85533482966, 93094250059, 99900916334, 106100115727, 111794330083, 117058642819, 121950096784, 126513296873, 130783951534, 134791211507, 138559270915, 142108496986, 145456247931, 148617478285, 151605195586, 154430810597, 157104409635, 159634968802, 162030524168, 164298308260, 166444860822, 168476120185, 170397500447, 172213958641, 173930055047, 175550008819, 177077750085, 178516968861, 179871160517, 181143667147, 182337714109, 183456441084, 184502927238, 185480210351, 186391300083, 187239185801, 188026839595, 188757215230, 189433243850, 190057827250, 190633829474, 191164067442, 191651301200, 192098224280, 192507454585, 192881526061, 193222881391, 193533865829, 193816722245, 194073587396, 194306489393, 194517346316, 194707965884, 194880046101, 195035176757, 195174841688, 195300421675, 195413197881, 195514355725, 195604989087, 195686104765, 195758627097, 195823402680, 195881205119, 195932739748, 195978648286, 196019513374, 196055862976, 196088174606, 196116879370, 196142365799, 196164983479, 196185046456, 196202836426, 196218605705, 196232579986, 196244960889, 196255928312, 196265642579, 196274246425, 196281866791, 196288616465, 196294595575, 196299892935, 196304587262, 196308748282, 196312437710, 196315710146, 196318613867, 196321191540, 196323480860, 196325515118, 196327323704, 196328932561, 196330364583, 196331639972, 196332776549, 196333790036, 196334694302, 196335501581, 196336222661, 196336867060, 196337443173, 196337958402, 196338419274, 196338831544, 196339200284, 196339529961, 196339824505, 196340087374, 196340321601, 196340529845, 196340714426, 196340877364, 196341020404, 196341145045, 196341252559, 196341344007, 196341420254, 196341481979, 196341529681, 196341563682, 196341584128, 196341590983]

theorem knot : (((7684911/50000000:ℚ):ℚ):ℝ) ≤ J (1/(((1:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (1:ℚ) (left i) (scores[i.val]?.getD 0) := by
    intro i
    fin_cases i
    · exact row000
    · exact row001
    · exact row002
    · exact row003
    · exact row004
    · exact row005
    · exact row006
    · exact row007
    · exact row008
    · exact row009
    · exact row010
    · exact row011
    · exact row012
    · exact row013
    · exact row014
    · exact row015
    · exact row016
    · exact row017
    · exact row018
    · exact row019
    · exact row020
    · exact row021
    · exact row022
    · exact row023
    · exact row024
    · exact row025
    · exact row026
    · exact row027
    · exact row028
    · exact row029
    · exact row030
    · exact row031
    · exact row032
    · exact row033
    · exact row034
    · exact row035
    · exact row036
    · exact row037
    · exact row038
    · exact row039
    · exact row040
    · exact row041
    · exact row042
    · exact row043
    · exact row044
    · exact row045
    · exact row046
    · exact row047
    · exact row048
    · exact row049
    · exact row050
    · exact row051
    · exact row052
    · exact row053
    · exact row054
    · exact row055
    · exact row056
    · exact row057
    · exact row058
    · exact row059
    · exact row060
    · exact row061
    · exact row062
    · exact row063
    · exact row064
    · exact row065
    · exact row066
    · exact row067
    · exact row068
    · exact row069
    · exact row070
    · exact row071
    · exact row072
    · exact row073
    · exact row074
    · exact row075
    · exact row076
    · exact row077
    · exact row078
    · exact row079
    · exact row080
    · exact row081
    · exact row082
    · exact row083
    · exact row084
    · exact row085
    · exact row086
    · exact row087
    · exact row088
    · exact row089
    · exact row090
    · exact row091
    · exact row092
    · exact row093
    · exact row094
    · exact row095
    · exact row096
    · exact row097
    · exact row098
    · exact row099
    · exact row100
    · exact row101
    · exact row102
    · exact row103
    · exact row104
    · exact row105
    · exact row106
    · exact row107
    · exact row108
    · exact row109
    · exact row110
    · exact row111
    · exact row112
    · exact row113
    · exact row114
    · exact row115
    · exact row116
    · exact row117
    · exact row118
    · exact row119
    · exact row120
    · exact row121
    · exact row122
    · exact row123
    · exact row124
    · exact row125
    · exact row126
    · exact row127
    · exact row128
  have h := lower_of_rows (lam:=(1:ℚ)) (target:=(7684911/50000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ1
