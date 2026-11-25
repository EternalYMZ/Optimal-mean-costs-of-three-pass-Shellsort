import Shellsort.F09WitnessBatch00
import Shellsort.F09WitnessBatch01
import Shellsort.F09WitnessBatch02
import Shellsort.F09WitnessBatch03
import Shellsort.F09WitnessBatch04
import Shellsort.F09WitnessBatch05
import Shellsort.F09WitnessBatch06
import Shellsort.F09WitnessBatch07
import Shellsort.F09WitnessBatch08
import Shellsort.F09WitnessBatch09
import Shellsort.F09WitnessBatch10
import Shellsort.F09WitnessBatch11
import Shellsort.F09WitnessBatch12
import Shellsort.F09WitnessBatch13
import Shellsort.F09WitnessBatch14
import Shellsort.F09WitnessBatch15
import Shellsort.F09Witness093

namespace Shellsort.F09
open Eval Quad
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def witnessScore (i : ℕ) : ℕ := (#[27464197336,40964606988,51870170445,60609464676,68291859793,75093751897,81228376976,86833821993,92005298391,96811676517,101304673576,105524306903,109502308126,113264356457,116831593857,120221685151,123449579571,126528070392,129468214452,132279652168,134970855469,137549322543,140021732728,142394071076,144671729571,146859590113,148962093143,150983294816,152926914962,154796377559,156594845078,158325247765,159990308719,161592565470,163134388626,164617998100,166045477318,167418785783,168739770299,170010175120,171231651248,172405765027,173534006190,174617795415,175658491456,176657397853,177615769234,178534817173,179415715582,180259605619,181067600062,181840787161,182580233937,183286988938,183962084471,184606538328,185221355038,185807526690,186366033367,186897843245,187403912402,187885184388,188342589603,188777044539,189189450910,189580694727,189951645337,190303154474,190636055323,190951161642,191249266949,191531143776,191797543025,192049193409,192286800999,192511048861,192722596807,192922081231,193110115048,193287287719,193454165363,193611290947,193759184550,193898343687,194029243703,194152338208,194268059565,194376819415,194479009233,194575000916,194665147387,194749783219,194829225268,194903773313,194973710700,195039304983,195100808560,195158459303,195212481177,195263084843,195310468251,195354817211,195396305944,195435097624,195471344880,195505190294,195536766862,195566198433,195593600133,195619078747,195642733085,195664654320,195684926290,195703625784,195720822786,195736580693,195750956504,195764000973,195775758724,195786268333,195795562370,195803667398,195810603926,195816386311,195821022612,195824514374,195826856352,195828036158] : Array ℕ)[i]?.getD 0

private theorem witness_rows (i : Fin 128) :
    RowCert true (40000/84681:ℚ) (middle i.val) (witnessScore i.val) := by
  fin_cases i
  · exact Witness.R000.checked
  · exact Witness.R001.checked
  · exact Witness.R002.checked
  · exact Witness.R003.checked
  · exact Witness.R004.checked
  · exact Witness.R005.checked
  · exact Witness.R006.checked
  · exact Witness.R007.checked
  · exact Witness.R008.checked
  · exact Witness.R009.checked
  · exact Witness.R010.checked
  · exact Witness.R011.checked
  · exact Witness.R012.checked
  · exact Witness.R013.checked
  · exact Witness.R014.checked
  · exact Witness.R015.checked
  · exact Witness.R016.checked
  · exact Witness.R017.checked
  · exact Witness.R018.checked
  · exact Witness.R019.checked
  · exact Witness.R020.checked
  · exact Witness.R021.checked
  · exact Witness.R022.checked
  · exact Witness.R023.checked
  · exact Witness.R024.checked
  · exact Witness.R025.checked
  · exact Witness.R026.checked
  · exact Witness.R027.checked
  · exact Witness.R028.checked
  · exact Witness.R029.checked
  · exact Witness.R030.checked
  · exact Witness.R031.checked
  · exact Witness.R032.checked
  · exact Witness.R033.checked
  · exact Witness.R034.checked
  · exact Witness.R035.checked
  · exact Witness.R036.checked
  · exact Witness.R037.checked
  · exact Witness.R038.checked
  · exact Witness.R039.checked
  · exact Witness.R040.checked
  · exact Witness.R041.checked
  · exact Witness.R042.checked
  · exact Witness.R043.checked
  · exact Witness.R044.checked
  · exact Witness.R045.checked
  · exact Witness.R046.checked
  · exact Witness.R047.checked
  · exact Witness.R048.checked
  · exact Witness.R049.checked
  · exact Witness.R050.checked
  · exact Witness.R051.checked
  · exact Witness.R052.checked
  · exact Witness.R053.checked
  · exact Witness.R054.checked
  · exact Witness.R055.checked
  · exact Witness.R056.checked
  · exact Witness.R057.checked
  · exact Witness.R058.checked
  · exact Witness.R059.checked
  · exact Witness.R060.checked
  · exact Witness.R061.checked
  · exact Witness.R062.checked
  · exact Witness.R063.checked
  · exact Witness.R064.checked
  · exact Witness.R065.checked
  · exact Witness.R066.checked
  · exact Witness.R067.checked
  · exact Witness.R068.checked
  · exact Witness.R069.checked
  · exact Witness.R070.checked
  · exact Witness.R071.checked
  · exact Witness.R072.checked
  · exact Witness.R073.checked
  · exact Witness.R074.checked
  · exact Witness.R075.checked
  · exact Witness.R076.checked
  · exact Witness.R077.checked
  · exact Witness.R078.checked
  · exact Witness.R079.checked
  · exact Witness.R080.checked
  · exact Witness.R081.checked
  · exact Witness.R082.checked
  · exact Witness.R083.checked
  · exact Witness.R084.checked
  · exact Witness.R085.checked
  · exact Witness.R086.checked
  · exact Witness.R087.checked
  · exact Witness.R088.checked
  · exact Witness.R089.checked
  · exact Witness.R090.checked
  · exact Witness.R091.checked
  · exact Witness.R092.checked
  · exact Witness.R093.checked
  · exact Witness.R094.checked
  · exact Witness.R095.checked
  · exact Witness.R096.checked
  · exact Witness.R097.checked
  · exact Witness.R098.checked
  · exact Witness.R099.checked
  · exact Witness.R100.checked
  · exact Witness.R101.checked
  · exact Witness.R102.checked
  · exact Witness.R103.checked
  · exact Witness.R104.checked
  · exact Witness.R105.checked
  · exact Witness.R106.checked
  · exact Witness.R107.checked
  · exact Witness.R108.checked
  · exact Witness.R109.checked
  · exact Witness.R110.checked
  · exact Witness.R111.checked
  · exact Witness.R112.checked
  · exact Witness.R113.checked
  · exact Witness.R114.checked
  · exact Witness.R115.checked
  · exact Witness.R116.checked
  · exact Witness.R117.checked
  · exact Witness.R118.checked
  · exact Witness.R119.checked
  · exact Witness.R120.checked
  · exact Witness.R121.checked
  · exact Witness.R122.checked
  · exact Witness.R123.checked
  · exact Witness.R124.checked
  · exact Witness.R125.checked
  · exact Witness.R126.checked
  · exact Witness.R127.checked

/-- Certified midpoint quadrature at the coprime witness. -/
theorem witness_upper_tight : J (1/(291/200:ℝ)^2) ≤ 149864981525/1000000000000 := by
  have result := upper_of_rows (lam:=(40000/84681:ℚ)) (target:=(149864981525/1000000000000:ℚ))
    (by norm_num) witnessScore (fun i hi => witness_rows ⟨i,hi⟩) (by decide +kernel)
  convert result using 1 <;> norm_num

theorem witness_upper_strict : J (1/(291/200:ℝ)^2) < 14986499/100000000 :=
  lt_of_le_of_lt witness_upper_tight (by norm_num)

theorem witness_upper : J (1/(291/200:ℝ)^2) ≤ 14986499/100000000 := witness_upper_strict.le

end Shellsort.F09
