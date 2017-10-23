namespace Tst.Core
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.Core
open Lib.SqTp
open Er
open VdtPrm 
open Brw
open MacroStr
open Fmt
open Lis
open StrSplit
open Term
open Prt
open Convert
[<AutoOpen>]
module Common = 
    let shouldThow f = try f()|>ignore; Assert.Fail "should throw, but not throw" with _ -> ()

[<TestClass>]
type Er() =
    [<TestMethod>]
    member x.er() =
        er "{sdf} sdkfjl {sdflkj}" [1;2]
    [<TestMethod>]
    member x.erLines() =
        let s = erLines "{ay} {sdf} sdkfjl {sdflkj} {sdjf}" [[1;2;3;4];"a\r\nb";1;2]
        brwStr s
        prtS s
    [<TestMethod>] 
    member x.erLines1() = 
        let d0 = ("","{a}lksdfldkf{b}",olis[12345,"...a...."])
        let tst(exp,macroStr,olis) =
            let run = fun() -> erLines macroStr olis
            let act = run()
            let r = act = exp
            if not r then 
                prtLisNL ["Dta-(macroStr,olis):\n%a";(macroStr,olis)]
                prtLisNL ["Act:\n%A";act]
                prtLisNL ["Exp:\n%A";exp]
            r |> Assert.IsTrue
        [d0] |> List.iter tst

[<TestClass>] 
type macroStr() = 
    [<TestMethod>] 
    member x.macroStrToSy() = 
        let d0 = ([|"{aa}";"{bb}"|],"sjkdfldksf {aa} klsdf ldkf  {bb}")
        let tst(exp,macroStr) =
            let run = fun() -> macroStrToSy macroStr
            let act = run()
            let r = act = exp
            if not r then 
                prtLisNL ["Dta:\n%a";macroStr]
                prtLisNL ["Act:\n%A";act]
                prtLisNL ["Exp:\n%A";exp]
            r |> Assert.IsTrue

        [d0] |> List.iter tst

open IxLin
[<TestClass>] 
type IxLin() = 
    [<TestMethod>] 
    member x.chkDupTermOne() = ()
(*        let s = Some "dup(a)"
        let n = None
        let d0 = (0,[|s;s;n;n|],[|"a klsdfj lsdfk";"a slkdfj";"dkf";"lksdfjdf"|])
        let d1 = (1,[|Some("dup(aaa)");n;Some("dup(aaa)")|], 
                    [|
                        "aaa sdklfsdklf"
                        "aa sdklfjsdfkl"
                        "aaa    sdklfdfk"
                    |])
        let d2 = (2,[|Some("dup()");Some("dup()");Some("dup()")|],[|"";"";""|])
        let tstr(case,exp:string option[],ly) =
            let run() = chkDupTermOne ly
            let act = run()
            let r = act = exp
            if not r then 
                prtLisNL["TstDta - ly\n";ly]
                prtLisNL["Act\n";act]
                prtLisNL["Exp\n";exp]
            Assert.IsTrue r
        [d0;d1;d2] |> List.iter tstr
        ()
*)
open Jn
[<TestClass>] 
type LyBk() = 
    [<TestMethod>]
    member x.tp'lyBkAy() = 
        let tst(cas,exp,sepLinPfx,(tp:string)) =
            let act = LyTp(sepLinPfx, tp)
            Assert.AreEqual(exp,act)
        let exp = [||]
        let tp = """==aa1
lksdf
==aa
a
a
==b
aa"""
        let sepLinPfx = "=="
        tst(0,exp,sepLinPfx,tp)

        let exp = [||]
        let tp = """==aa1
lksdf
==aa
a
a
==b
aa"""
        let sepLinPfx = "=="
        tst(1,exp,sepLinPfx,tp)

[<TestClass>] 
type Fmt() = 
    [<TestMethod>] 
    member x.fmtQQ() = 
        let d0 = ("","",olis[1;1])
        let d1 = ("","",olis[1;1])
        let d2 = ("","",olis[1;1])
        let tst(exp,qqStr,olis:obj list) =
            let run = fun() -> fmtQQ qqStr olis
            let act = run()
            let r = act = exp
            if not r then 
                prtLisNL ["Dta:\n%a";(qqStr,olis)]
                prtLisNL ["Act:\n%A";act]
            r |> Assert.IsTrue

        [d0;d1;d2] |> List.iter tst

[<TestClass>]
type StrOp() = 
    [<TestMethod>] 
    member x.string()= 
        let t0:obj = null
        let d0:string*obj
            = (    "[(1, 2); (3, 4)]",
                    box [(1,2);(3,4)])
        let d1 = ( "(sdf, 3)",
                    box ("sdf",3))
        let d2 = ( "1",box 1 )
        let tstThow v = shouldThow (fun()->string v)
        let tst(exp,v) =
                let act = oToStr v
                let r = act = exp
                if not r then ()
                else
                    printf "v = %A" v
                    printf "act = %s" act
                    printf "exp = %s" exp
                Assert.IsTrue r
        [d0;d1;d2] |> List.iter tst
        [t0] |> List.iter tstThow

[<TestClass>] 
type Brw() = 
    [<TestMethod>] 
    member x.brwAy() = 
        brwOy[|1;2|]
        brwOy[|3;"a"|]

[<TestClass>]
type Term() = 
    [<TestMethod>]
    member x.brkNTerm() =
        let run lin atMost exp = assert(brkNTerm atMost lin = exp)
        run "a b c "   2 [|"a";"b"|]
        run "a b c "   3 [|"a";"b";"c"|]
        run "a b c "   4 [|"a";"b";"c"|]
        run "  a b c " 2 [|"a";"b"|]
        run "  a b c " 3 [|"a";"b";"c"|]
        run "  a b c " 4 [|"a";"b";"c"|]

    [<TestMethod>]
    member x.shiftTerm() =
        let run lin exp = Assert.AreEqual(exp,shiftTerm lin)                      
        run "a b c " ("a","b c")
