import Shellsort.F09CertificateLowerJ11d8A
import Shellsort.F09CertificateLowerJ11d8B
import Shellsort.F09CertificateLowerJ11d8C
import Shellsort.F09CertificateLowerJ11d8D

namespace Shellsort.F09.Quad.LowerJ11d8
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 57520853976, 66114146591, 73575658413, 80222222730, 86242881610, 91761346207, 96863924589, 101613736338, 106058646560, 110236012688, 114175682939, 117901975077, 121435030140, 124791766984, 127986572873, 131031814316, 133938222296, 136715187745, 139370991624, 141912986482, 144347741478, 146681159475, 148918572502, 151064820286, 153124315353, 155101097367, 156998878775, 158821083350, 160570878901, 162251205181, 163864797832, 165414209072, 166901825741, 168329885215, 169700489629, 171015618770, 172277141931, 173486828940, 174646360503, 175757337961, 176821292471, 177839693631, 178813957485, 179745453891, 180635513182, 181485432081, 182296478852, 183069897649, 183806912096, 184508728096, 185176535927, 185811511667, 186414818014, 186987604582, 187531007735, 188046150045, 188534139446, 188996068159, 189433011451, 189846026290, 190236149959, 190604398655, 190951766139, 191279222449, 191587712711, 191878156071, 192151444751, 192408443253, 192649987710, 192876885375, 193089914273, 193289822981, 193477330554, 193653126577, 193817871341, 193972196127, 194116703593, 194251968254, 194378537040, 194496929926, 194607640624, 194711137323, 194807863475, 194898238613, 194982659190, 195061499446, 195135112275, 195203830103, 195267965770, 195327813393, 195383649232, 195435732536, 195484306372, 195529598433, 195571821828, 195611175839, 195647846662, 195682008108, 195713822285, 195743440247, 195771002611, 195796640143, 195820474321, 195842617854, 195863175183, 195882242943, 195899910397, 195916259842, 195931366983, 195945301275, 195958126241, 195969899754, 195980674296, 195990497179, 195999410744, 196007452522, 196014655372, 196021047573, 196026652896, 196031490629, 196035575569, 196038917967, 196041523434, 196043392793, 196044521874, 196044901249]

theorem knot : (((7533711/50000000:ℚ):ℚ):ℝ) ≤ J (1/(((11/8:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (64/121:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(64/121:ℚ)) (target:=(7533711/50000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ11d8
