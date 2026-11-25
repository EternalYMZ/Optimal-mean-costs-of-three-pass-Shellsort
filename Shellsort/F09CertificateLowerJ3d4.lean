import Shellsort.F09CertificateLowerJ3d4A
import Shellsort.F09CertificateLowerJ3d4B
import Shellsort.F09CertificateLowerJ3d4C
import Shellsort.F09CertificateLowerJ3d4D

namespace Shellsort.F09.Quad.LowerJ3d4
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 63401393462, 76998842147, 88157015281, 97718904427, 106120464399, 113622809619, 120397473760, 126564594424, 132212379356, 137407988780, 142204056241, 146642813985, 150758819325, 154580821811, 158133079522, 161436308488, 164508380148, 167364843086, 170019323604, 172483846543, 174769107245, 176884715222, 178839419708, 180641318513, 182298045889, 183816932976, 185205135251, 186469724129, 187617743090, 188656231635, 189592222407, 190432717830, 191184652763, 191854849161, 192449967841, 192976461367, 193440530994, 193848089639, 194204732012, 194515712350, 194785929731, 195019920546, 195221857486, 195395554234, 195544475000, 195671748004, 195780182036, 195872285297, 195950285770, 196016152472, 196071617029, 196118195091, 196157207214, 196189798905, 196216959597, 196239540414, 196258270603, 196273772607, 196286575755, 196297128600, 196305809954, 196312938681, 196318782351, 196323564806, 196327472773, 196330661590, 196333260138, 196335375083, 196337094491, 196338490913, 196339623984, 196340542626, 196341286898, 196341889539, 196342377264, 196342771838, 196343090966, 196343349034, 196343557716, 196343726473, 196343862968, 196343973401, 196344062783, 196344135165, 196344193816, 196344241376, 196344279975, 196344311332, 196344336832, 196344357594, 196344374520, 196344388338, 196344399635, 196344408887, 196344416476, 196344422712, 196344427846, 196344432082, 196344435583, 196344438484, 196344440892, 196344442895, 196344444566, 196344445963, 196344447134, 196344448117, 196344448944, 196344449643, 196344450233, 196344450734, 196344451159, 196344451520, 196344451828, 196344452091, 196344452315, 196344452505, 196344452668, 196344452806, 196344452923, 196344453021, 196344453102, 196344453168, 196344453221, 196344453261, 196344453290, 196344453307, 196344453312]

theorem knot : (((1937887/12500000:ℚ):ℚ):ℝ) ≤ J (1/(((3/4:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (16/9:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(16/9:ℚ)) (target:=(1937887/12500000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ3d4
