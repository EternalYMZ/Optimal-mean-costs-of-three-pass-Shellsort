import Shellsort.F09CertificateLowerJ7d4A
import Shellsort.F09CertificateLowerJ7d4B
import Shellsort.F09CertificateLowerJ7d4C
import Shellsort.F09CertificateLowerJ7d4D

namespace Shellsort.F09.Quad.LowerJ7d4
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 0, 58833199414, 65538202101, 71530407033, 76976515101, 81985506455, 86633333553, 90975484098, 95053990280, 98901620605, 102544526730, 106003989482, 109297612890, 112440165801, 115444190526, 118320452896, 121078281520, 123725827907, 126270268932, 128717966558, 131074595356, 133345245441, 135534506381, 137646536213, 139685118683, 141653711080, 143555484482, 145393357846, 147170027051, 148887989769, 150549566885, 152156921021, 153712072622, 155216913984, 156673221521, 158082666544, 159446824742, 160767184564, 162045154643, 163282070412, 164479200010, 165637749593, 166758868129, 167843651769, 168893147848, 169908358568, 170890244435, 171839727454, 172757694132, 173644998311, 174502463819, 175330886985, 176131038986, 176903668049, 177649501497, 178369247630, 179063597458, 179733226259, 180378794980, 181000951466, 181600331538, 182177559903, 182733250921, 183268009221, 183782430189, 184277100325, 184752597496, 185209491076, 185648342009, 186069702784, 186474117355, 186862120998, 187234240132, 187590992105, 187932884960, 188260417178, 188574077426, 188874344300, 189161686070, 189436560441, 189699414330, 189950683657, 190190793162, 190420156241, 190639174805, 190848239175, 191047727986, 191238008129, 191419434712, 191592351044, 191757088645, 191913967275, 192063294978, 192205368156, 192340471640, 192468878797, 192590851626, 192706640881, 192816486192, 192920616197, 193019248667, 193112590643, 193200838568, 193284178407, 193362785770, 193436826024, 193506454392, 193571816036, 193633046128, 193690269902, 193743602677, 193793149862, 193839006929, 193881259353, 193919982519, 193955241585, 193987091302, 194015575780, 194040728203, 194062570479, 194081112813, 194096353211, 194108276889, 194116855584, 194122046755, 194123792651]

theorem knot : (((14622049/100000000:ℚ):ℚ):ℝ) ≤ J (1/(((7/4:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (16/49:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(16/49:ℚ)) (target:=(14622049/100000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ7d4
