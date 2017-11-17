Drop Table #Tx

Drop Table #TxMbr

Drop Table #MbrDta

Drop Table #Div

Drop Table #Sto

Drop Table #Crd

Drop Table #Cnt

Drop Table #Oup

Drop Table #MbrWs

Select
                                     Y  ,
      Sum(SHAmount)                  Amt,
      Sum(SHQty)                     Qty,
      Count(SHInvoice+SHSDate+SHRef) Cnt
   Into      #Tx
   From      SalesHistory
   Where     bet between "str" and "%%DteFm %%DteTo"
   And       str in (Div %LisDiv)
   And       str in (Sto %LisSto)
   And       str in (Crd %LisCrd)
   Group By   
Select Distinct
      JCMCode Mbr
   From      #Tx
   Into      #TxMbr
Select
      x.Mbr                                                    Mbr ,
      DATEDIFF(YEAR,CONVERT(DATETIME ,x.JCMDOB,112),GETDATE()) Age ,
      a.JCMSex                                                 Sex ,
      a.JCMStatus                                              Sts ,
      a.JCMDist                                                Dist,
      a.JCMArea                                                Area
   From      #TxMbr x
   Join      JCMMember a on x.Mbr = a.JCMMCode
   Into      #MbrDta



Select
                                     Y  ,
      Sum(SHAmount)                  Amt,
      Sum(SHQty)                     Qty,
      Count(SHInvoice+SHSDate+SHRef) Cnt
   Into      #Oup
   From      #Tx x
   Left Join #Crd a on x.Crd = a.Crd
   Left Join #Div b on x.Div = b.Div
   Left Join #Sto c on x.Sto = c.Sto
   Left Join #MbrDta d on x.Mbr = d.Mbr
   Where     JCMCode in (Select Mbr From #TxMbr)
Select
      Count(*)   RecCnt,
      Sum(TxCnt) TxCnt ,
      Sum(Qty)   Qty   ,
      Sum(Amt)   Amt   
   Into      #Cnt
   From      #Tx