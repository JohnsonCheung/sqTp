namespace Tst.SqTp
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.Core
[<TestClass>] 
type Dup() = 
    [<TestMethod>] 
    member x.syFstTermDupMsg() =
        let s = Some "dup(a)"
        let n = None
        let d0 = (0,[|s;s;n;n|],[|"a klsdfj lsdfk";"a slkdfj";"dkf";"lksdfjdf"|])
        let d1 = (1,[|Some("dup(aaa)");n;Some("dup(aaa)")|], 
                    [|
                        "aaa sdklfsdklf"
                        "aa sdklfjsdfkl"
                        "aaa    sdklfdfk"
                    |])
        let d2 = (2,[|Some("dup()");Some("dup()");Some("dup()")|],[|"";"";""|])
        let tstr(case,exp,ly) =
            let run() = syFstTermDupMsg ly
            let act = run()
            let r = act = exp
            if not r then erLines "{case} {ly} {Act} {Exp}" [case;ly;act;exp] |> prtS
            Assert.IsTrue r
        [d0;d1;d2] |> List.iter tstr