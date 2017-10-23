namespace Tst
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib
open Lib.Sql3
[<AutoOpen>]
module Common = 
    let shouldThow f = try f()|>ignore; Assert.Fail "should throw, but not throw" with _ -> ()
    let sqTp = """
-- Rmk: -- is remark
-- %XX: is prmDicLin
-- %?XX: is switchPrm, it value must be 0 or 1
-- ?XX: is switch line
-- SwitchLin: is ?XXX [OR|AND|EQ|NE] [SwPrm_OR_AND|SwPrm_EQ_NE]
-- SwPrm_OR_AND: SwTerm ..
-- SwPrm_EQ_NE:  SwEQ_NE_T1 SwEQ_NE_T2
-- SwEQ_NE_T1: 
-- SwEQ_NE_T2: 
-- SwTerm:     ?XX|%?XX     -- if %?XX, its value only 1 or 0 is allowed
-- Only one gp of %XX:
-- Only one gp of ?XX:
-- All other gp is sql-statement or sql-statements
-- sql-statments: Drp xxx xxx
-- sql-statment: [sel|selDis|upd|into|fm|whBetStr|whBetNbr|whInStrLis|whInNbrLis|andInNbrLis|andInStrLis|gp|jn|left|expr]
-- optional: Whxxx and Andxxx can have ?-pfx becomes: ?Whxxx and ?Andxxx.  The line will become empty
==============================================
Drp Tx TxMbr MbrDta Div Sto Crd Cnt Oup MbrWs
=============================================
%?BrkMbr 0
%?BrkSto 0
%?BrkCrd 0
%?BrkDiv 0
%SumLvl  Y
%?MbrEmail
%?MbrNm
%?MbrPhone
%?MbrAdr
%%DteFm 20170101
%%DteTo 20170131
%LisDiv 1 2
%LisSto
%LisCrd
%CrdExpr ...
============================================
?LvlY    EQ %SumLvl Y
?LvlM    EQ %SumLvl M
?LvlW    EQ %SumLvl W
?LvlD    EQ %SumLvl D
?Y       OR ?LvlD ?LvlW ?LvlM ?LvlY
?M       OR ?LvlD ?LvlW ?LvlM
?W       OR ?LvlD ?LvlW
?D       OR ?LvlD
?Dte     OR ?LvlD
?Mbr     OR %BrkMbr
?MbrCnt  OR %BrkMbr
?Div     OR %BrkDiv
?Sto     OR %?BrkSto
?Crd     OR %?BrkCrd
?sel#Div NE %LisDiv *blank
?sel#Sto NE %LisSto *blank
?sel#Crd NE %LisCrd *blank
============================================= #Tx
sel  ?Crd ?Mbr ?Div ?Sto ?Y ?M ?W ?WD ?D ?Dte Amt Qty Cnt 
into #Tx
fm   SalesHistory
whBetStr     %%DteFm %%DteTo
?andInStrLis Div %LisDiv
?andInStrLis Sto %LisSto
?andInNbrLis Crd %LisCrd
?gp ?Crd ?Mbr ?Div ?Sto ?Crd ?Y ?M ?W ?WD ?D ?Dte
$Crd %CrdExpr
$Mbr JCMCode
$Sto
$Y
$M
$W
$WD
$D
$Dte
Amt Sum(SHAmount)
$Qty Sum(SHQty)
$Cnt Count(SHInvoice+SHSDate+SHRef)
============================================= #TxMbr
selDis  Mbr
fm      #Tx
into    #TxMbr
============================================= #MbrDta
sel   Mbr Age Sex Sts Dist Area
fm    #TxMbr x
jn    JCMMember a on x.Mbr = a.JCMMCode
into  #MbrDta
$Mbr  x.Mbr
$Age  DATEDIFF(YEAR,CONVERT(DATETIME ,x.JCMDOB,112),GETDATE())
$Sex  a.JCMSex
$Sts  a.JCMStatus
$Dist a.JCMDist
$Area a.JCMArea
==-=========================================== #Div
?sel Div DivNm DivSeq DivSts
fm   Division
into #Div
?whInStrLis Div %LisDiv
$Div Dept + Division
$DivNm LongDies
$DivSeq Seq
$DivSts Status
============================================ #Sto
?sel Sto StoNm StoCNm
fm   Location
into #Sto
?whInStrLis Loc %LisLoc
$Sto
$StoNm
$StoCNm
============================================= #Crd
?sel        Crd CrdNm
fm          Location
into        #Crd
?whInNbrLis Crd %LisCrd
$Crd
$CrdNm
============================================= #Oup
sel  ?Crd ?CrdNm ?Mbr ?Age ?Sex ?Sts ?Dist ?Area ?Div ?DivNm ?Sto ?StoNm ?StoCNm ?Y ?M ?W ?WD ?D ?Dte Amt Qty Cnt
into #Oup
fm   #Tx x
left #Crd a on x.Crd = a.Crd
left #Div b on x.Div = b.Div
left #Sto c on x.Sto = c.Sto
left #MbrDta d on x.Mbr = d.Mbr
wh   JCMCode in (Select Mbr From #TxMbr)
============================================ #Cnt
sel ?MbrCnt RecCnt TxCnt Qty Amt
into #Cnt
fm  #Tx
$MbrCnt Count(Distinct Mbr)
$RecCnt Count(*)
$TxCnt  Sum(TxCnt)
$Qty    Sum(Qty)
$Amt    Sum(Amt)
============================================
"""


[<TestClass>]
type Sql3() = 
    [<TestMethod>]
    member x.main() = 
        ()
            
    //    [<TestMethod>]
    //    member x.get3Lvl() = sql3 |> splitCrLf |> get3LvlLy |> brwSy
    
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
module lyDupTermOneChk__Tst = 
    type tstDta = {case:int; isThow: bool; exp:string option[]; ly :string[]}
    [<TestClass>] 
    type tst() = 
        [<TestMethod>] 
        member x.lyDupTermOneChk() =
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
                let run() = lyDupTermOneChk ly
                let act = run()
                let r = act = exp
                if not r then 
                    prtLisNL["TstDta - ly\n";ly]
                    prtLisNL["Act\n";act]
                    prtLisNL["Exp\n";exp]
                Assert.IsTrue r
            [d0;d1;d2] |> List.iter tstr
[<TestClass>]
type prmLyVdt_Tst() =
    [<TestMethod>]
    member x.prmLyVdt() = 
        let tstThow ly = shouldThow(fun()->prmLyVdt ly)
        let tst(ly,exp) =
            let act = prmLyVdt ly
            let r = act=exp
            if not r then
                printfn "tstDta\n%A" ly
                printfn "act\n%A" act
                printfn "exp\n%A" exp
            Assert.IsTrue r
        let d0 =(   [|  "%ab 1234"
                        "%ab 1234 12 3"
                        "%xyz";"%dd"|],
                    (true, syJnCrLf [|  "%ab 1234       ---(dup(%ab))"
                                        "%ab 1234 12 3  ---(dup(%ab))" 
                                        "%xyz          " 
                                        "%dd           " |]))
        [d0] |> List.iter tst

[<TestClass>] 
type erLines_Tst() = 
    [<TestMethod>] 
    member x.erLines() = 
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
type macroStrToSy_Tst() = 
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

[<TestClass>] 
type fmtQQ_Tst() = 
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
type string_Tst() = 
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
module brwAy =
    [<TestClass>] 
    type x() = 
        [<TestMethod>] 
        member x.brwAy() = 
            brwOy[|1;2|]
            brwOy[|3;"a"|]
            