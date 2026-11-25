import Shellsort.F09CertificateRows

/-! Finite row witnesses for the signed Fourier quadrature. -/
namespace Shellsort.F09.Quad.LowerJ1d2
open Shellsort.F09.Eval
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def seed096 : Box := ⟨20010138818229809945876545645724275,20010138818229827635982735785801296⟩
private def modes096 : Array Box := #[⟨20010138818229809945876545645724275,20010138818229827635982735785801297⟩, ⟨0,1⟩]

theorem row096 : RowCert false (4:ℚ) 18432 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 18432 * scoreScale
  rw [row_cached (d:=(207/256:ℚ)) (seed:=seed096) (es:=modes096)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed097 : Box := ⟨13393920032273993886293490811626075,13393920032274006026937173002863670⟩
private def modes097 : Array Box := #[⟨13393920032273993886293490811626075,13393920032274006026937173002863671⟩, ⟨0,1⟩]

theorem row097 : RowCert false (4:ℚ) 18818 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 18818 * scoreScale
  rw [row_cached (d:=(219784831/268435456:ℚ)) (seed:=seed097) (es:=modes097)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed098 : Box := ⟨9027991255417797857489050010419373,9027991255417806241656380923386385⟩
private def modes098 : Array Box := #[⟨9027991255417797857489050010419373,9027991255417806241656380923386386⟩, ⟨0,1⟩]

theorem row098 : RowCert false (4:ℚ) 19208 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 19208 * scoreScale
  rw [row_cached (d:=(13904191/16777216:ℚ)) (seed:=seed098) (es:=modes098)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed099 : Box := ⟨6129849954069013767665736724729855,6129849954069019595878751837883527⟩
private def modes099 : Array Box := #[⟨6129849954069013767665736724729855,6129849954069019595878751837883528⟩, ⟨0,1⟩]

theorem row099 : RowCert false (4:ℚ) 19602 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 19602 * scoreScale
  rw [row_cached (d:=(225099567/268435456:ℚ)) (seed:=seed099) (es:=modes099)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed100 : Box := ⟨4194061898142421833012013063023827,4194061898142425912632493358040327⟩
private def modes100 : Array Box := #[⟨4194061898142421833012013063023827,4194061898142425912632493358040328⟩, ⟨0,1⟩]

theorem row100 : RowCert false (4:ℚ) 20000 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 20000 * scoreScale
  rw [row_cached (d:=(889375/1048576:ℚ)) (seed:=seed100) (es:=modes100)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed101 : Box := ⟨2892668250961434940297463783081297,2892668250961437816807540109627651⟩
private def modes101 : Array Box := #[⟨2892668250961434940297463783081297,2892668250961437816807540109627652⟩, ⟨0,1⟩]

theorem row101 : RowCert false (4:ℚ) 20402 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 20402 * scoreScale
  rw [row_cached (d:=(230205967/268435456:ℚ)) (seed:=seed101) (es:=modes101)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed102 : Box := ⟨2011848533006541749869613438663617,2011848533006543793620949037784818⟩
private def modes102 : Array Box := #[⟨2011848533006541749869613438663617,2011848533006543793620949037784819⟩, ⟨0,1⟩]

theorem row102 : RowCert false (4:ℚ) 20808 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 20808 * scoreScale
  rw [row_cached (d:=(14542191/16777216:ℚ)) (seed:=seed102) (es:=modes102)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed103 : Box := ⟨1411498369735955205813006060838424,1411498369735956669545651386459687⟩
private def modes103 : Array Box := #[⟨1411498369735955205813006060838424,1411498369735956669545651386459688⟩, ⟨0,1⟩]

theorem row103 : RowCert false (4:ℚ) 21218 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 21218 * scoreScale
  rw [row_cached (d:=(235084831/268435456:ℚ)) (seed:=seed103) (es:=modes103)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed104 : Box := ⟨999334894732748483129618112686064,999334894732749540248549102917537⟩
private def modes104 : Array Box := #[⟨999334894732748483129618112686064,999334894732749540248549102917538⟩, ⟨0,1⟩]

theorem row104 : RowCert false (4:ℚ) 21632 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 21632 * scoreScale
  rw [row_cached (d:=(57967/65536:ℚ)) (seed:=seed104) (es:=modes104)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed105 : Box := ⟨714242931082830925903715107856406,714242931082831696048647409212228⟩
private def modes105 : Array Box := #[⟨714242931082830925903715107856406,714242931082831696048647409212229⟩, ⟨0,1⟩]

theorem row105 : RowCert false (4:ℚ) 22050 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 22050 * scoreScale
  rw [row_cached (d:=(239716575/268435456:ℚ)) (seed:=seed105) (es:=modes105)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed106 : Box := ⟨515519698744335576885941122908136,515519698744336143082236086231499⟩
private def modes106 : Array Box := #[⟨515519698744335576885941122908136,515519698744336143082236086231500⟩, ⟨0,1⟩]

theorem row106 : RowCert false (4:ℚ) 22472 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 22472 * scoreScale
  rw [row_cached (d:=(15120847/16777216:ℚ)) (seed:=seed106) (es:=modes106)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed107 : Box := ⟨375898606944438904977524975500516,375898606944439325189333866380790⟩
private def modes107 : Array Box := #[⟨375898606944438904977524975500516,375898606944439325189333866380791⟩, ⟨0,1⟩]

theorem row107 : RowCert false (4:ℚ) 22898 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 22898 * scoreScale
  rw [row_cached (d:=(244081231/268435456:ℚ)) (seed:=seed107) (es:=modes107)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed108 : Box := ⟨277003693052461774189642700769974,277003693052462089137135604140875⟩
private def modes108 : Array Box := #[⟨277003693052461774189642700769974,277003693052462089137135604140876⟩, ⟨0,1⟩]

theorem row108 : RowCert false (4:ℚ) 23328 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 23328 * scoreScale
  rw [row_cached (d:=(961551/1048576:ℚ)) (seed:=seed108) (es:=modes108)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed109 : Box := ⟨206373809550255290361116837172612,206373809550255528834555677955731⟩
private def modes109 : Array Box := #[⟨206373809550255290361116837172612,206373809550255528834555677955732⟩, ⟨0,1⟩]

theorem row109 : RowCert false (4:ℚ) 23762 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 23762 * scoreScale
  rw [row_cached (d:=(248158447/268435456:ℚ)) (seed:=seed109) (es:=modes109)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed110 : Box := ⟨155504908565948838725723948114333,155504908565949021215435498030326⟩
private def modes110 : Array Box := #[⟨155504908565948838725723948114333,155504908565949021215435498030327⟩, ⟨0,1⟩]

theorem row110 : RowCert false (4:ℚ) 24200 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 24200 * scoreScale
  rw [row_cached (d:=(15630175/16777216:ℚ)) (seed:=seed110) (es:=modes110)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed111 : Box := ⟨118555573517018190957537715078434,118555573517018332145960426247479⟩
private def modes111 : Array Box := #[⟨118555573517018190957537715078434,118555573517018332145960426247480⟩, ⟨0,1⟩]

theorem row111 : RowCert false (4:ℚ) 24642 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 24642 * scoreScale
  rw [row_cached (d:=(251927487/268435456:ℚ)) (seed:=seed111) (es:=modes111)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed112 : Box := ⟨91486621062889539948909648697771,91486621062889650430316478716594⟩
private def modes112 : Array Box := #[⟨91486621062889539948909648697771,91486621062889650430316478716595⟩, ⟨0,1⟩]

theorem row112 : RowCert false (4:ℚ) 25088 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 25088 * scoreScale
  rw [row_cached (d:=(3871/4096:ℚ)) (seed:=seed112) (es:=modes112)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed113 : Box := ⟨71486141635669705192276158123069,71486141635669792665883123432550⟩
private def modes113 : Array Box := #[⟨71486141635669705192276158123069,71486141635669792665883123432551⟩, ⟨0,1⟩]

theorem row113 : RowCert false (4:ℚ) 25538 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 25538 * scoreScale
  rw [row_cached (d:=(255367231/268435456:ℚ)) (seed:=seed113) (es:=modes113)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed114 : Box := ⟨56583164977747476041545702458871,56583164977747546143828904230155⟩
private def modes114 : Array Box := #[⟨56583164977747476041545702458871,56583164977747546143828904230156⟩, ⟨0,1⟩]

theorem row114 : RowCert false (4:ℚ) 25992 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 25992 * scoreScale
  rw [row_cached (d:=(16059807/16777216:ℚ)) (seed:=seed114) (es:=modes114)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed115 : Box := ⟨45386606149753637253473269820014,45386606149753694142088607666339⟩
private def modes115 : Array Box := #[⟨45386606149753637253473269820014,45386606149753694142088607666340⟩, ⟨0,1⟩]

theorem row115 : RowCert false (4:ℚ) 26450 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 26450 * scoreScale
  rw [row_cached (d:=(258456175/268435456:ℚ)) (seed:=seed115) (es:=modes115)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed116 : Box := ⟨36907853973373652252852924555284,36907853973373699018681264546756⟩
private def modes116 : Array Box := #[⟨36907853973373652252852924555284,36907853973373699018681264546757⟩, ⟨0,1⟩]

theorem row116 : RowCert false (4:ℚ) 26912 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 26912 * scoreScale
  rw [row_cached (d:=(1015087/1048576:ℚ)) (seed:=seed116) (es:=modes116)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed117 : Box := ⟨30439501844905361428133738031165,30439501844905400387793953626345⟩
private def modes117 : Array Box := #[⟨30439501844905361428133738031165,30439501844905400387793953626346⟩, ⟨0,1⟩]

theorem row117 : RowCert false (4:ℚ) 27378 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 27378 * scoreScale
  rw [row_cached (d:=(261172431/268435456:ℚ)) (seed:=seed117) (es:=modes117)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed118 : Box := ⟨25471969952280709986672096652594,25471969952280742891477580929222⟩
private def modes118 : Array Box := #[⟨25471969952280709986672096652594,25471969952280742891477580929223⟩, ⟨0,1⟩]

theorem row118 : RowCert false (4:ℚ) 27848 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 27848 * scoreScale
  rw [row_cached (d:=(16398991/16777216:ℚ)) (seed:=seed118) (es:=modes118)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed119 : Box := ⟨21635846373883920518042742361110,21635846373883948704252251415217⟩
private def modes119 : Array Box := #[⟨21635846373883920518042742361110,21635846373883948704252251415218⟩, ⟨0,1⟩]

theorem row119 : RowCert false (4:ℚ) 28322 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 28322 * scoreScale
  rw [row_cached (d:=(263493727/268435456:ℚ)) (seed:=seed119) (es:=modes119)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed120 : Box := ⟨18661788193542661331058855317357,18661788193542685828678918269188⟩
private def modes120 : Array Box := #[⟨18661788193542661331058855317357,18661788193542685828678918269189⟩, ⟨0,1⟩]

theorem row120 : RowCert false (4:ℚ) 28800 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 28800 * scoreScale
  rw [row_cached (d:=(64575/65536:ℚ)) (seed:=seed120) (es:=modes120)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed121 : Box := ⟨16352487158896658237374749375426,16352487158896679849566070405003⟩
private def modes121 : Array Box := #[⟨16352487158896658237374749375426,16352487158896679849566070405004⟩, ⟨0,1⟩]

theorem row121 : RowCert false (4:ℚ) 29282 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 29282 * scoreScale
  rw [row_cached (d:=(265397407/268435456:ℚ)) (seed:=seed121) (es:=modes121)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed122 : Box := ⟨14562981121082488989658385984288,14562981121082508351217468958843⟩
private def modes122 : Array Box := #[⟨14562981121082488989658385984288,14562981121082508351217468958844⟩, ⟨0,1⟩]

theorem row122 : RowCert false (4:ℚ) 29768 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 29768 * scoreScale
  rw [row_cached (d:=(16636591/16777216:ℚ)) (seed:=seed122) (es:=modes122)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed123 : Box := ⟨13186784630471488349874536311896,13186784630471505970790003338852⟩
private def modes123 : Array Box := #[⟨13186784630471488349874536311896,13186784630471505970790003338853⟩, ⟨0,1⟩]

theorem row123 : RowCert false (4:ℚ) 30258 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 30258 * scoreScale
  rw [row_cached (d:=(266860431/268435456:ℚ)) (seed:=seed123) (es:=modes123)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed124 : Box := ⟨12146117494693217745530283351243,12146117494693234043904705175220⟩
private def modes124 : Array Box := #[⟨12146117494693217745530283351243,12146117494693234043904705175221⟩, ⟨0,1⟩]

theorem row124 : RowCert false (4:ℚ) 30752 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 30752 * scoreScale
  rw [row_cached (d:=(1044607/1048576:ℚ)) (seed:=seed124) (es:=modes124)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed125 : Box := ⟨11385059230892958385057387102474,11385059230892973712506471327516⟩
private def modes125 : Array Box := #[⟨11385059230892958385057387102474,11385059230892973712506471327517⟩, ⟨0,1⟩]

theorem row125 : RowCert false (4:ℚ) 31250 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 31250 * scoreScale
  rw [row_cached (d:=(267859375/268435456:ℚ)) (seed:=seed125) (es:=modes125)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed126 : Box := ⟨10864836853972459334162081430668,10864836853972473995996982251572⟩
private def modes126 : Array Box := #[⟨10864836853972459334162081430668,10864836853972473995996982251573⟩, ⟨0,1⟩]

theorem row126 : RowCert false (4:ℚ) 31752 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 31752 * scoreScale
  rw [row_cached (d:=(16761087/16777216:ℚ)) (seed:=seed126) (es:=modes126)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed127 : Box := ⟨10560721807478817552201699111954,10560721807478831824163058314879⟩
private def modes127 : Array Box := #[⟨10560721807478817552201699111954,10560721807478831824163058314880⟩, ⟨0,1⟩]

theorem row127 : RowCert false (4:ℚ) 32258 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 32258 * scoreScale
  rw [row_cached (d:=(268370431/268435456:ℚ)) (seed:=seed127) (es:=modes127)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

private def seed128 : Box := ⟨10460209586773191309170076635577,10460209586773205452147737543575⟩
private def modes128 : Array Box := #[⟨10460209586773191309170076635577,10460209586773205452147737543576⟩, ⟨0,1⟩]

theorem row128 : RowCert false (4:ℚ) 32768 196344454640 := by
  change _ ≤ rowValue false (4:ℚ) 32768 * scoreScale
  rw [row_cached (d:=(1:ℚ)) (seed:=seed128) (es:=modes128)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end Shellsort.F09.Quad.LowerJ1d2
