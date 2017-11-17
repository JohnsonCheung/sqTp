#nowarn "58"
namespace Lib.SqTp.T
(*
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.SqTp
open Lib.Core
open Lib.SqTp.Tst.Dta1
open Lib.SqTp.ZTyp
[<AutoOpen>]
module Dta =
    let mutable dtaNo = 0
    let mutable sqTpBkTy = ZTyp.SqBk
    let mutable bkAy = Tp.bkAy aSqTp
    let mutable prm = BkAy.prm bkAy
    let mutable swSdic = BkAy.sw bkAy
    let mutable swLy = BkAy.swLy bkAy
    let mutable sw = SwLy.evl prm swLy
    let mutable swBrkAy = swLy |> ayMap SwLin.brk 
    let mutable empSw = ZTyp.empSw
    let mutable andOrTerm1 = "aa"
    let mutable tpLy = aSqTp |> splitCrLf
module Lin =
    let isSq() = 
        let x lin =
            let isSq = if Lin.isSq lin then "true" else ""
            sprintf "%6s %s" isSq lin
        tpLy |> ayMap x |> brwSy
module AndOrTerm1 =
    let evl() = AndOrTerm1.evl prm sw andOrTerm1
    let chk() = AndOrTerm1.chk  prm sw andOrTerm1 
module BkAy =
    let evl() = BkAy.evl bkAy
    let ly() = BkAy.ly sqTpBkTy
module SwBrkAy =
    let evl() = SwBrkAy.evl prm sw swBrkAy
(*
namespace Lib.SqTp.TClass
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.SqTp.Tst.Dta1
open Lib.SqTp.T
*)
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