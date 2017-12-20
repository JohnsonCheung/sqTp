#nowarn "58"
namespace Lib.SqTp2.Tst
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.SqTp2
open Lib.SqTp2.Types
open Lib.Core
open Lib
[<TestClass>]
type SqWh() =
    [<TestMethod>]
    member x.whDta() =
        let t whDtaStr exp =
            let act = sqWhDta whDtaStr
            let r = exp=act
            Assert.IsTrue(r)
        t "$ aa"          (WhConst ("aa"))
        t "f in  str a b" (WhInStr ("f","a b"))
        t "f in  nbr a b" (WhInNbr ("f","a b"))
        t "f bet str a b" (WhBetStr("f","a","b"))
        t "f bet nbr a b" (WhBetNbr("f","a","b"))
        t "f lik     a b" (WhLik   ("f","a b"))
[<TestClass>]
type SqLin() =
    [<TestMethod>]
    member x.ty() =
        let t lin ty =
            let act = sqLinTy lin //"Drp").ty 
            let exp = ty
            Assert.AreEqual(exp,act)
        t "Drp" Drp
        t "Sel a" Sel
        t "sel a" Sel
        t "sel a" Sel
        t "sEL a" Sel
        t "upd a" Upd
        t "seldis a" SelDis
        t "set a" Set
        t "fm a" Fm
        t "gp a" Gp
        t "wh bet1 str a b" Wh
        t "and bet str" And
        t "left a" Left
        t "jn a" Jn
    [<TestMethod>]
    member x.sqLines() =
        let edic = empSdic
        let t lin exp=
            let act = sqLines lin edic
            Assert.AreEqual(exp,act)
        t "sel    a b c"    ""
        t "seldis a b c"    ""
        t "upd    a b c"    ""
        t "set    a b c"    ""
        t "fm     a b c"    ""
        t "gp     a b c"    ""
        t "wh     a b c"    ""
        t "and    a b c"    ""
        t "left   a b c"    ""
        t "jn     a b c"    ""
        t "wh b lik a%"          "where b like 'a%'"
        t "wh $ a>100"           "where a>100"
        t "wh f in  str 1 2 3 4" "where f in ('1','2','3','4')"
        t "wh f in  nbr 1 2 3 4" "where f in (1,2,3,4)"
        t "wh f bet nbr 1 2"     "where f between 1 and 2"
        t "wh f bet str 1 2"     "where f between '1' and '2'"
(*
[<TestClass>]type BkAy () =
    [<TestMethod>]member x.evl() = 
        let act = BkAy.evl()
        let exp = ""
        //       Assert.AreEqual(exp,act) 
        ()
[<TestClass>]type SwBrkAy () =
    [<TestMethod>]member x.evl() =
        let act = SwBrkAy.evl()
        let exp = ""
        //       Assert.AreEqual(exp,act) 
        ()
[<TestClass>]type SwLinChk() =
    [<TestMethod>]member x.``Term_MustExist_in_Prm_or_Sw``() = 
        let sw = sdicByLy [|"?BrkS 1"|]
        let prm = sdicByLy [|"%A 1"|]
        let tst swLin = 
            let exp:string list = []
            let act = SwLinChk.Term_MustExist_in_Prm_or_Sw prm sw swLin
            Assert.AreEqual (exp,act)
        let tstF swLin msg = 
            let act = SwLinChk.Term_MustExist_in_Prm_or_Sw prm sw swLin
            Assert.AreEqual (msg,act)
        tst "%Sw EQ ?BrkS %A"
        tst "%Sw NE ?BrkS %A"
        tst "%Sw AND ?BrkS %A"
        tst "%Sw OR ?BrkS %A"
        tst "%Sw AND ?BrkS %A %A"
        tst "%Sw OR ?BrkS %A %A"
        tstF "%Sw OR ?BrkS %A1" ["term(%A1) not found in prm"]
        tstF "%Sw OR ?BrkS1 %AB" ["term(?BrkS1) not found in sw"; "term(%AB) not found in prm"]
        tstF "%Sw EQ ?BrkS1 %AB %A" ["term(?BrkS1) not found in sw"; "term(%AB) not found in prm"]
[<TestClass>]type SwLy    () =
    [<TestMethod>]member x.evl() = 
        let prm = prm
        let swLy = swLy
        let act = SwLy.evl prm swLy
        //brwDic act
        ()
    [<TestMethod>]member x.vdt() = 
        let act = SwLy.vdt prm swLy
        let exp = false, """?LvlY    EQ %SumLvl Y
?LvlM    EQ %SumLvl M
?LvlW    EQ %SumLvl W
?LvlD    EQ %SumLvl D
?Y       OR ?LvlD ?LvlW ?LvlM ?LvlY
?M       OR ?LvlD ?LvlW ?LvlM
?W       OR ?LvlD ?LvlW
?D       OR ?LvlD
?Dte     OR ?LvlD
?Mbr     OR %?BrkMbr
?MbrCnt  OR %?BrkMbr
?Div     OR %?BrkDiv
?Sto     OR %?BrkSto
?Crd     OR %?BrkCrd
?sel#Div NE %LisDiv *blank
?sel#Sto NE %LisSto *blank
?sel#Crd NE %LisCrd *blank"""
        Assert.AreEqual(exp,act)
[<TestClass>]type Ly      () =
    [<TestMethod>]member x.``Ly.ty: should be SqBk``() =
        let tst line0 line1 =
            let act = Ly.ty [|line0;line1|]
            let exp = ZTyp.SqBk
            Assert.AreEqual(exp,act)
        tst "sel"     ""
        tst "seldis"  ""
        tst "upd aa"  ""
        tst "drp"     ""
        tst "Sel"     ""
        tst "Seldis"  ""
        tst "Upd aa"  ""
        tst "Drp"     ""
        tst "?sel"    "xx"
        tst "?seldis" "xx"
        tst "?upd"    "xx"
        tst "?Sel"    "xx"
        tst "?Seldis" "xx"
        tst "?Upd"    "xx"
    [<TestMethod>]member x.``Ly.ty: should not be SqBk, sw.  Because ?-lines is more than non-?-line``() =
        let tst line0 =
            let act = Ly.ty [|line0|]
            let exp = ZTyp.SwBk
            Assert.AreEqual(exp,act)
        tst "?sel"    
        tst "?seldis"
        tst "?upd"
[<TestClass>]type PrmLin  () =
    [<TestMethod>]member x.``chk should return no error (None)``() = 
        let tst lin = 
            let act = PrmLin.chk lin
            Assert.IsNull act
        tst "%ldsf sldf df"
        tst "%?ldsf 1"
        tst "%?ldsf 0"
    [<TestMethod>]member x.``chk should return some er (Some string)``() = 
        let tst erMsg lin = 
            let act = PrmLin.chk lin
            Assert.AreEqual(Some erMsg,act)
        tst "must have pfx-(%)"                     "aldsf sldf df"
        tst "for %?, it should have only 2 terms"   "%?aldsf sldf df"
        tst "for %?, 2nd term must be 0 or 1"       "%?aldsf df"
[<TestClass>]type PrmLy   () =
    [<TestMethod>]member x.``chk should be no error and no change in tp``() =
        let tst ly = 
            let act_isEr,act_tp = PrmLy.vdt ly
            let exp_isEr = false
            let exp_tp = ly |> jnCrLf
            Assert.AreEqual(exp_isEr,act_isEr)
            Assert.AreEqual(exp_tp  ,act_tp  )
        tst [|  "%ab 1234"
                "%ab 1234 12 3"
                "%xyz"
                "%dd"|]
        tst [|  "%ab 1234       ---(dup(%ab))"
                "%ab 1234 12 3  ---(dup(%ab))" 
                "%xyz          " 
                "%dd           " |]
    [<TestMethod>]member x.``chk should be no error and but tp is modified``() =
        let tst ly exp_tp =
            let act_isEr,act_tp = PrmLy.vdt ly
            let exp_isEr = false
            Assert.AreEqual(exp_isEr,act_isEr)
            Assert.AreEqual(exp_tp  ,act_tp  )
        tst [|  "%ab 1234"
                "%ab 1234 12 3"
                "%xyz"
                "%dd"|] 
            [|  "%ab 1234"
                "%ab 1234 12 3"
                "%xyz"
                "%dd"|] 
                
        tst [|  "%ab 1234       ---(dup(%ab))"
                "%ab 1234 12 3  ---(dup(%ab))" 
                "%xyz          " 
                "%dd           " |]
[<TestClass>]type SqTp    () = 
    [<TestMethod>]member x.evl() =
        let act = sqTpEvl aSqTp
        brwObj act
        let exp = {tp'=Some "";sq'=Some ""}
        Assert.AreEqual(exp,act)
module main =
    [<EntryPointAttribute>]
    let main args =
        BkAy().evl()
        //Ly().``Ly.ty: should be SqBk``()
        //SqTp().evl()
        //SwBrkAy().evl()
        //SwLy().vdt()
        //SwLy().evl()
        //SwLinChk().``Term_MustExist_in_Prm_or_Sw``()
        0
*)
module main =
    let aa b =
        let a = 1
        let b = 2
        let c = 3
        ()
    [<EntryPoint>]
    let main args =
        aa()
        aa()
        0