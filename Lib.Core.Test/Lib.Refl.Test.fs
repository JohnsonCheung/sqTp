namespace Lib.Refl.Tst
open Microsoft.VisualStudio.TestTools.UnitTesting
open Lib.Core
open Lib.Refl
type aa = Apple | Orange 
type bb = Apple' = 1 | Orange' = 2
[<TestClass>] 
type Union() = 
    [<TestMethod>] 
    member x.isUnion() =
        let act = isUnion<aa>
        let exp = true
        Assert.AreEqual(exp,act)
    member x.assertIsUnion() =
        assertIsUnion<bb>

module Main =
    [<EntryPoint>]
    let main args = 
        Union().assertIsUnion()
        0