namespace Lib.Dta.Tst
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.Core
open Lib.Dta
[<TestClass>] 
type Dt() = 
    [<TestMethod>] 
    member x.dtFmtLy() =
        let sdr0:obj[] = [|1;2;3;4|]
        let sdr1:obj[] = [|"aaa";"b";"c";"d"|]
        let drs = drs "aaa bb cccccc ddddd" "Txt Txt Txt Txt" [|sdr0;sdr1|]
        let dt = dt "Dt" drs
        brwAy (dtFmtLy dt)
module Main =
    [<EntryPoint>]
    let main args = 
        Dt().dtFmtLy()
        0