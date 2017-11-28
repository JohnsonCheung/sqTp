namespace Lib.SqTp3.Types
open Lib.Core
open Lib.Tp
open Lib.LyVdt
open Lib.Dta
open Lib.Refl
open Lib.LyVdt
type sqTpFt = ft
type sqTpNm = nm
type prmLy = ly
type swLy = ly
type prmLyAy = prmLy[]
type swLyAy = swLy[]
type sqLin = lin
type sqL0 = sqLin
type sqLy = sqLin[]
type sqStmt = lines
type sqStmts = lines
type ftEdtRslt =Done|Cancel
type tpOpt = tp option
type sqOpt = sqStmts option
type runRslt = tpOpt*sqOpt
type tpNm = nm
type tpFt = ft
type sqFt = ft
type tpChanged = bool
type sqChanged = bool
type edtRslt = Cancel|Saved of tpChanged*sqChanged*tpFt*sqFt
type sqTpPth = pth
type sqTp = tp
type erTerm = term  // error term
type eTerm = string // expression term
type sqTerm = string
type exprLines = lines
type edic = Map<eTerm,lines>
type termWdt = int
type exprWdt = int
type sqpCxt = lines
type sqpKey = term  /// always have width of 10 char   
//------------------------------
type expr = sdic
type exprLin = string
type swLgcStr = string
//------------------------------
/// expression terms, started with $
type sqFmLin = sqLin
type sqUpdLin = sqLin
type sqIntoLin = sqLin
type sqKey = term
type sqRst = termLvs
//---------------------------------
type clnSqLy = ly
type clnLy = ly
type tpLy = ly
type sqpPfx = string
type qTy = PrmBk|SwBk|SqBk|RmkBk|ErBk
type sqpTy = Sel|SelDis|Upd|Set|Fm|Into|Gp|Jn|Left|Wh|And
//------------------------------
type sw = bdic
type prmSdic = sdic
type swSdic = sdic
type swLin = lin
type swKey = key
type andOr = AND|OR
type eqNe = EQ|NE
type swTerm = term
type swT1 = term
type swT2 = term
type swLgc = SwAndOr of andOr*swTerm[] | SwEqNe of eqNe*swT1*swT2
type swBrk = {lin:swLin;k:swKey;lgc:swLgc option}
type prm = sdic
namespace Lib.SqTp3
open Lib.Core
open Lib.Tp
open Lib.LyVdt
open Lib.Dta
open Lib.Refl
open Lib.LyVdt
open Lib.SqTp3.Types