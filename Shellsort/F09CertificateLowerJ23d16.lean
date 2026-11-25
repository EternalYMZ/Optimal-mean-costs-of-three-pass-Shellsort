import Shellsort.F09CertificateLowerJ23d16A
import Shellsort.F09CertificateLowerJ23d16B
import Shellsort.F09CertificateLowerJ23d16C
import Shellsort.F09CertificateLowerJ23d16D

namespace Shellsort.F09.Quad.LowerJ23d16
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 56289848144, 64712237885, 72030130256, 78553132015, 84465935857, 89889381880, 94907757583, 99582691747, 103960908785, 108078867681, 111965692073, 115645103736, 119136745230, 122457112454, 125620229275, 128638146520, 131521318240, 134278890295, 136918925040, 139448578623, 141874242597, 144201658240, 146436009785, 148582001103, 150643919305, 152625687870, 154530911305, 156362912914, 158124766888, 159819325715, 161449243680, 163016997134, 164524902066, 165975129458, 167369718822, 168710590267, 169999555393, 171238327239, 172428529493, 173571705086, 174669324274, 175722792256, 176733456346, 177702612702, 178631512576, 179521368071, 180373357354, 181188629316, 181968307640, 182713494289, 183425272397, 184104708596, 184752854800, 185370749474, 185959418448, 186519875317, 187053121485, 187560145893, 188041924518, 188499419655, 188933579067, 189345335025, 189735603290, 190105282078, 190455251025, 190786370190, 191099479119, 191395395980, 191674916786, 191938814718, 192187839553, 192422717198, 192644149335, 192852813172, 193049361304, 193234421670, 193408597607, 193572468001, 193726587508, 193871486867, 194007673266, 194135630781, 194255820866, 194368682884, 194474634687, 194574073224, 194667375176, 194754897611, 194836978659, 194913938191, 194986078506, 195053685021, 195117026956, 195176358011, 195231917036, 195283928690, 195332604079, 195378141383, 195420726461, 195460533439, 195497725270, 195532454278, 195564862670, 195595083033, 195623238797, 195649444672, 195673807068, 195696424474, 195717387819, 195736780804, 195754680196, 195771156107, 195786272228, 195800086047, 195812649018, 195824006711, 195834198920, 195843259735, 195851217573, 195858095168, 195863909517, 195868671777, 195872387097, 195875054406, 195876666119, 195877207774]

theorem knot : (((1875377/12500000:ℚ):ℚ):ℝ) ≤ J (1/(((23/16:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (256/529:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(256/529:ℚ)) (target:=(1875377/12500000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ23d16
