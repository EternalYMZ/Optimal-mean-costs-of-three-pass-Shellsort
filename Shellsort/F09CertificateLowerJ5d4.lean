import Shellsort.F09CertificateLowerJ5d4A
import Shellsort.F09CertificateLowerJ5d4B
import Shellsort.F09CertificateLowerJ5d4C
import Shellsort.F09CertificateLowerJ5d4D

namespace Shellsort.F09.Quad.LowerJ5d4
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 60246140531, 69214505351, 76989913914, 83905310768, 90159443631, 95882436263, 101165113831, 106073931717, 110659309757, 114960619428, 119009334748, 122831112010, 126447212854, 129875507882, 133131202893, 136227376165, 139175383715, 141985170179, 144665510937, 147224203192, 149668218599, 152003826465, 154236694135, 156371969438, 158414348901, 160368134516, 162237281284, 164025437302, 165735977826, 167372034568, 168936521225, 170432156128, 171861482704, 173226888281, 174530621629, 175774809443, 176961471881, 178092537154, 179169855089, 180195209560, 181170329672, 182096899588, 182976566937, 183810949758, 184601642004, 185350217647, 186058233489, 186727230785, 187358735823, 187954259614, 188515296855, 189043324305, 189539798739, 190006154605, 190443801522, 190854121697, 191238467395, 191598158493, 191934480214, 192248681066, 192541971026, 192815519990, 193070456504, 193307866775, 193528793963, 193734237741, 193925154120, 194102455507, 194267010996, 194419646855, 194561147206, 194692254853, 194813672269, 194926062687, 195030051303, 195126226558, 195215141484, 195297315097, 195373233833, 195443352992, 195508098194, 195567866838, 195623029541, 195673931560, 195720894180, 195764216081, 195804174649, 195841027256, 195875012488, 195906351327, 195935248280, 195961892454, 195986458586, 196009108013, 196029989593, 196049240576, 196066987420, 196083346562, 196098425140, 196112321666, 196125126661, 196136923236, 196147787644, 196157789786, 196166993678, 196175457887, 196183235932, 196190376648, 196196924526, 196202920017, 196208399813, 196213397100, 196217941782, 196222060687, 196225777739, 196229114115, 196232088379, 196234716584, 196237012362, 196238986979, 196240649379, 196242006189, 196243061705, 196243817846, 196244274076, 196244427291]

theorem knot : (((15183639/100000000:ℚ):ℚ):ℝ) ≤ J (1/(((5/4:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (16/25:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(16/25:ℚ)) (target:=(15183639/100000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ5d4
