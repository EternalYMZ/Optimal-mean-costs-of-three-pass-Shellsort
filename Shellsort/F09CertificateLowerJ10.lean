import Shellsort.F09CertificateLowerJ10A
import Shellsort.F09CertificateLowerJ10B
import Shellsort.F09CertificateLowerJ10C
import Shellsort.F09CertificateLowerJ10D

namespace Shellsort.F09.Quad.LowerJ10
open Shellsort.F09.Eval
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def scores : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53630476650, 54973435616, 56278694957, 57548719457, 58785695221, 59991571636, 61168095547, 62316839332, 63439224154, 64536539380, 65609958893, 66660554899, 67689309672, 68697125610, 69684833880, 70653201897, 71602939815, 72534706187, 73449112921, 74346729638, 75228087508, 76093682657, 76943979175, 77779411809, 78600388359, 79407291822, 80200482322, 80980298843, 81747060787, 82501069390, 83242609000, 83971948233, 84689341028, 85395027607, 86089235347, 86772179578, 87444064314, 88105082921, 88755418727, 89395245585, 90024728388, 90644023546, 91253279417, 91852636714, 92442228871, 93022182382, 93592617122, 94153646629, 94705378374, 95247914005, 95781349574, 96305775746, 96821277989, 97327936746, 97825827604, 98315021432, 98795584522, 99267578706, 99731061468, 100186086042, 100632701505, 101070952850, 101500881057, 101922523153, 102335912266, 102741077661, 103138044779, 103526835259, 103907466959, 104279953961, 104644306576, 105000531335, 105348630977, 105688604422, 106020446747, 106344149140, 106659698859, 106967079172, 107266269295, 107557244316, 107839975116, 108114428272, 108380565958, 108638345828, 108887720894, 109128639388, 109361044615, 109584874788, 109800062854, 110006536306, 110204216970, 110393020786, 110572857565, 110743630728, 110905237024, 111057566224, 111200500793, 111333915534, 111457677205, 111571644101, 111675665606, 111769581708, 111853222474, 111926407476, 111988945174, 112040632247, 112081252863, 112110577880, 112128363992, 112134352776]

theorem knot : (((7830839/100000000:ℚ):ℚ):ℝ) ≤ J (1/(((10:ℚ):ℚ):ℝ)^2) := by
  have cert : ∀ i : Fin 129, RowCert false (1/100:ℚ) (left i) (scores[i.val]?.getD 0) := by
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
  have h := lower_of_rows (lam:=(1/100:ℚ)) (target:=(7830839/100000000:ℚ)) (by norm_num) (fun i => scores[i]?.getD 0)
    (fun i hi => cert ⟨i,hi⟩) (by decide +kernel)
  norm_num at h ⊢
  exact h

end Shellsort.F09.Quad.LowerJ10
