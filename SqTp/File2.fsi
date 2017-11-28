namespace aa
(*
namespace Lib1.Core
[<AutoOpen>]
module ZTyp =
    type isEr = bool
    type ly = string[]
    type lines = string
    type sdic = Map<string,string>
    type bdic = Map<string,bool>
    type lin = string
    type ix = int
    type ft = string
    type msg = string

namespace Lib1.Tp
module ZTyp =
    open Lib1.Core
    type linPfx = string
    type bkLy = ly
    type tpLy = ly
    type bk = {fstLinStr:string;mutable ly:ly}
    type tp = lines
    type tpFt = ft
module H1 =
    open Lib1.Core
    open ZTyp
    val bkToLines : (bk -> lines)
    val tpBkAyToLines: (bk[] -> lines)
module H2 =
    open Lib1.Core
    open ZTyp
    val brkTpFt : (linPfx -> tpFt -> bk[])
    val brkTp : (linPfx -> tp -> bk[])

    val toLyLis : (linPfx -> tpLy -> bkLy list)
    val toBk : (linPfx -> bkLy -> bk)
module Tp =
    open Lib1.Core
    open ZTyp
    val brkTp : (linPfx -> tp -> bk[])
    val brkTpFt : (linPfx -> tpFt -> bk[])
    val tpBkAyToLines : (bk[] -> lines)

namespace Lib1.ChkLy
module ZTyp =
    open Lib1.Core
    type ix = int
    type ixLin = { ix:ix; lin: lin }
    type ixMsg = { ix:ix; msg: msg }
    type ixAyLy = ix[]*ly
    type linChkr = lin -> msg option
    type bkChkr = ly -> msg list[]
    type linPred = lin -> bool
    type chkTermOneDup = bool
    type skipLinFunOpt = ( lin -> bool ) option
    type newTp = lines
    type tp = lines
    type chkr = linChkr list * bkChkr list * chkTermOneDup * skipLinFunOpt 
    type rslt = isEr * newTp
module H =
    open Lib1.Core
    open ZTyp
    val mkIxMsg    : ix*msg -> ixMsg
    val ixMsgPutLy : ixMsg list -> ly -> lines
    val applyChkLinFun : ixAyLy -> linChkr -> ixMsg list 
    val applyChkBkFun  : ixAyLy -> bkChkr -> ixMsg list
    val fstTermDupBkChkr : bkChkr
    val skipLy : skipLinFunOpt -> ly -> ixAyLy 

                                                    /// kkd
                                                    /// skldf sldkf
    val chkLy : (chkr -> ly -> rslt)
    
    
    val chkTp : (chkr -> tp -> rslt)
module ChkLy =
    open ZTyp
    open Lib1.Core
    val chkTp : (chkr -> tp -> rslt)
    val chkLy : (chkr -> ly -> rslt)

namespace Lib2.SqTp
module TstDta =
    open Lib1.Core
    val sqTp:lines
type rslt = { tp': string option; sq' : string option }
module ZTyp =
    open Lib.Core 
    open Lib
    open Lib1.Core
    //------------------------------
    type swTerm = string
    type swT1 = string
    type swT2 = string
    //------------------------------
    type expr = sdic
    type exprLin = string
    //------------------------------
    type sqLin = lin
    type sqTp = lines
    type sqLy = ly
    type clnSqLy = ly
    type sqStmt = lines
    type sqTpFt = ft
    type sqpPfx = string
    type sqpCxt = string
    type sqTpBkTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
    type sqLinTy = Sel|SelDis|Upd|Set|Fm|Gp|Jn|Left|Wh|And
    type sqTpBk = {ty:sqTpBkTy;mutable tpBk:Tp.bk}
    //------------------------------
    type swOp = AND|OR|EQ|NE
    type swTerms = TermAy of swTerm[] | T1T2 of swT1*swT2
    type sw = Map<string,bool>
    type swSdic = sdic
    type swLin = string
    type swKey = string
    type swLy = swLin[]
    type swBrk = {lin:swLin;k:swKey;op:swOp option;terms:swTerms option}
    //------------------------------
    type prm = sdic
    val empSw:sw
    val empPrm:prm 
open ZTyp

module EvlSqLy =
    module H =
        val SqLy'isDrp: clnSqLy->bool
        val SqLy'isSkip: sw -> clnSqLy -> bool 
//        val SqLy'choose:  cond lis = 
//        val aySplit : ('a->bool->'a[]) 
    val evlSqLy : prm -> sw -> sqLy -> sqStmt
module EvlTp = 
    module H =
        open Lib1.Core
        val processRslt:sqTpFt->rslt->unit
        val mkBk: Lib.Tp.bk -> sqTpBk 
    val sqTpEvl : (sqTp -> rslt)
    val sqTpFtEvl : (sqTpFt -> unit)

module SqTp =
    val sqTpEvl : (sqTp -> rslt)
    val sqTpFtEvl : (sqTpFt -> unit)
*)
