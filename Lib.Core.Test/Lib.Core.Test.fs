namespace Lib.Core.Tst
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.Core
[<TestClass>]
type Core() = 
    [<TestMethod>]
    member x.fstTermDupMsgOptAy() =
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
            let run() = ly_dupFstTermMsgOptAy ly
            let act = run()
            let r = act = exp
            if not r then erLines "{case} {ly} {Act} {Exp}" [case;ly;act;exp] |> prt
            Assert.IsTrue r
        [d0;d1;d2] |> List.iter tstr

    [<TestMethod>]
    member x.erLines() =
//------------------------------------------
        let exp = ""
        let olis = [box 1]
        let macroStr = "{int}"
        let act = erLines macroStr olis
        Assert.AreEqual(exp,act)
//------------------------------------------
        let exp = ""
        let olis = [box 1]
        let macroStr = "{int}"
        let act = erLines macroStr olis
        Assert.AreEqual(exp,act)
