namespace Lib.Core.Tst
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.Core
[<TestClass>]
type Core() =
    [<TestMethod>]
    member x.dupFmTo() =
        let lis=[1;2;3;4;4;4;5]
        let act = dupFmTo lis
        let exp = Some(3,5)
        assert(act = exp)
        //
        let lis=[1;2;3;4;5;6]
        let act = dupFmTo lis
        let exp = None
        assert(act = exp)
    [<TestMethod>]
    member x.ayRplByFmTo() =
        let ay = [|1;2;3;4;5|]
        let fmTo = 1,2
        let by = [|9;10;11|]
        let act = ayRplByFmTo by fmTo ay
        let exp = [|1;9;10;11;4;5|]
        assert(act=exp)
    [<TestMethod>]
    member x.brkNTerm() =
        let t n s exp =
            let act = brkNTerm n s
            let t = exp=act
            Assert.IsTrue(t)
        t 2 "aa bb"          [|"aa";"bb"   |]
        t 2 "aa bb cc"       [|"aa";"bb cc"|]
        t 3 "aa bb"          [|"aa";"bb";""     |]
        t 3 "aa bb cc"       [|"aa";"bb";"cc"   |]
        t 3 "aa bb cc dd"    [|"aa";"bb";"cc dd"|]
        t 4 "aa bb cc"       [|"aa";"bb";"cc";""     |]
        t 4 "aa bb cc dd"    [|"aa";"bb";"cc";"dd"   |]
        t 4 "aa bb cc dd ee" [|"aa";"bb";"cc";"dd ee"|]
        t 5 "aa bb cc"          [|"aa";"bb";"cc";""  ;""     |]
        t 5 "aa bb cc dd"       [|"aa";"bb";"cc";"dd";""     |]
        t 5 "aa bb cc dd"       [|"aa";"bb";"cc";"dd";""     |]
        t 5 "aa bb cc dd ee"    [|"aa";"bb";"cc";"dd";"ee"   |]
        t 5 "aa bb cc dd ee ff" [|"aa";"bb";"cc";"dd";"ee ff"|]
    [<TestMethod>]
    member x.lyCombineSamFstTerm() =
        let ly = splitVbar "aa xyz  |aa bbccdd|aa 1234"
        let act = lyCombineSamFstTerm ly    
        let exp = "aa xyz bbccdd 1234"
        assert(act=exp)
        //
        let ly = splitVbar "aaa xyz  |aa bbccdd|aa 1234"
        try 
            let act = lyCombineSamFstTerm ly
            assert false
        with e ->
            assert (e.Message = "{ly} should have all same fst-term")
    [<TestMethod>]
    member x.quoteSng() =
        let act = quoteSng "s"
        let exp = "'s'"
        Assert.AreEqual(exp,act)
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
            let run() = lyDupFstTermMsgOptAy ly
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
