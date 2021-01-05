// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

namespace Microsoft.FSharp.Collections

open System
open System.Collections
open System.Collections.Generic
open System.Diagnostics
open System.Text
open Microsoft.FSharp.Core
open Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators
open Microsoft.FSharp.Core.Operators
open Microsoft.FSharp.Collections

module SetImplementation = 
    module internal Sorting =


        let inline private mergeSeq (cmp : IComparer<'Key>) (li : int) (ri : int) (len : int) (src : ('Key * 'Value)[]) (dst : ('Key * 'Value)[]) (length : int) =
            let le = ri
            let re = min length (ri + len)
            let mutable oi = li
            let mutable li = li
            let mutable ri = ri

            while li < le && ri < re do
                let lv = src.[li]
                let rv = src.[ri]
                let c = cmp.Compare(fst lv, fst rv)
                if c <= 0 then
                    dst.[oi] <- lv
                    oi <- oi + 1
                    li <- li + 1
                else
                    dst.[oi] <- rv
                    oi <- oi + 1
                    ri <- ri + 1

            while li < le do
                dst.[oi] <- src.[li]
                oi <- oi + 1
                li <- li + 1
                
            while ri < re do
                dst.[oi] <- src.[ri]
                oi <- oi + 1
                ri <- ri + 1

        let inline private mergeSeqHandleDuplicates (cmp : IComparer<'Key>) (li : int) (ri : int) (len : int) (src : ('Key * 'Value)[]) (dst : ('Key * 'Value)[]) (length : int) =
            let le = ri
            let re = min length (ri + len)
            let start = li
            let mutable oi = li
            let mutable li = li
            let mutable ri = ri
            let mutable lastValue = Unchecked.defaultof<'Key * 'Value>

            let inline append (v : ('Key * 'Value)) =
                if oi > start && cmp.Compare(fst v, fst lastValue) = 0 then
                    dst.[oi-1] <- v
                    lastValue <- v
                else
                    dst.[oi] <- v
                    lastValue <- v
                    oi <- oi + 1

            while li < le && ri < re do
                let lv = src.[li]
                let rv = src.[ri]
                let c = cmp.Compare(fst lv, fst rv)
                if c <= 0 then
                    append lv
                    li <- li + 1
                else
                    append rv
                    ri <- ri + 1

            while li < le do
                append src.[li]
                li <- li + 1
                
            while ri < re do
                append src.[ri]
                ri <- ri + 1

            oi
        
        // assumes length > 2
        let mergeSortHandleDuplicates (mutateArray : bool) (cmp : IComparer<'Key>) (arr : ('Key * 'Value)[]) (length : int) =
            let mutable src = Array.zeroCreate length
            let mutable dst = 
                // mutateArray => allowed to mutate arr
                if mutateArray then arr
                else Array.zeroCreate length

            // copy to sorted pairs
            let mutable i0 = 0
            let mutable i1 = 1
            while i1 < length do
                let va = arr.[i0]
                let vb = arr.[i1]
                let c = cmp.Compare(fst va, fst vb)
                if c <= 0 then
                    src.[i0] <- va
                    src.[i1] <- vb
                else
                    src.[i0] <- vb
                    src.[i1] <- va
                    
                i0 <- i0 + 2
                i1 <- i1 + 2

            if i0 < length then
                src.[i0] <- arr.[i0]
                i0 <- i0 + 1


            // merge sorted parts of length `sortedLength`
            let mutable sortedLength = 2
            let mutable sortedLengthDbl = 4
            while sortedLengthDbl < length do
                let mutable li = 0
                let mutable ri = sortedLength

                // merge case
                while ri < length do
                    mergeSeq cmp li ri sortedLength src dst length
                    li <- ri + sortedLength
                    ri <- li + sortedLength

                // right got empty
                while li < length do
                    dst.[li] <- src.[li]
                    li <- li + 1
                    
                // sortedLength * 2
                sortedLength <- sortedLengthDbl
                sortedLengthDbl <- sortedLengthDbl <<< 1
                // swap src and dst
                let t = dst
                dst <- src
                src <- t

            // final merge-dedup run
            let cnt = mergeSeqHandleDuplicates cmp 0 sortedLength sortedLength src dst length
            struct(dst, cnt)

        let inline private mergeSeqV (cmp : IComparer<'Key>) (li : int) (ri : int) (len : int) (src : KeyValuePair<'Key, 'Value>[]) (dst : KeyValuePair<'Key, 'Value>[]) (length : int) =
            let le = ri
            let re = min length (ri + len)
            let mutable oi = li
            let mutable li = li
            let mutable ri = ri

            while li < le && ri < re do
                let (KeyValue(lk, lv)) = src.[li]
                let (KeyValue(rk, rv)) = src.[ri]
                let c = cmp.Compare(lk, rk)
                if c <= 0 then
                    dst.[oi] <- KeyValuePair(lk, lv)
                    oi <- oi + 1
                    li <- li + 1
                else
                    dst.[oi] <- KeyValuePair(rk, rv)
                    oi <- oi + 1
                    ri <- ri + 1

            while li < le do
                dst.[oi] <- src.[li]
                oi <- oi + 1
                li <- li + 1
                
            while ri < re do
                dst.[oi] <- src.[ri]
                oi <- oi + 1
                ri <- ri + 1

        let inline private mergeSeqHandleDuplicatesV (cmp : IComparer<'Key>) (li : int) (ri : int) (len : int) (src : KeyValuePair<'Key, 'Value>[]) (dst : KeyValuePair<'Key, 'Value>[]) (length : int) =
            let le = ri
            let re = min length (ri + len)
            let start = li
            let mutable oi = li
            let mutable li = li
            let mutable ri = ri
            let mutable lastKey = Unchecked.defaultof<'Key>

            let inline append k v =
                if oi > start && cmp.Compare(k, lastKey) = 0 then
                    dst.[oi-1] <- KeyValuePair(k,v)
                    lastKey <- k
                else
                    dst.[oi] <- KeyValuePair(k,v)
                    lastKey <- k
                    oi <- oi + 1

            while li < le && ri < re do
                let (KeyValue(lk, lv)) = src.[li]
                let (KeyValue(rk, rv)) = src.[ri]
                let c = cmp.Compare(lk, rk)
                if c <= 0 then
                    append lk lv
                    li <- li + 1
                else
                    append rk rv
                    ri <- ri + 1

            while li < le do
                let (KeyValue(k,v)) = src.[li]
                append k v
                li <- li + 1
                
            while ri < re do
                let (KeyValue(k,v)) = src.[ri]
                append k v
                ri <- ri + 1

            oi
        
        // assumes length > 2
        let mergeSortHandleDuplicatesV (mutateArray : bool) (cmp : IComparer<'Key>) (arr : KeyValuePair<'Key, 'Value>[]) (length : int) =
            let mutable src = Array.zeroCreate length
            let mutable dst = 
                // mutateArray => allowed to mutate arr
                if mutateArray then arr
                else Array.zeroCreate length

            // copy to sorted pairs
            let mutable i0 = 0
            let mutable i1 = 1
            while i1 < length do
                let (KeyValue(ka,va)) = arr.[i0] 
                let (KeyValue(kb,vb)) = arr.[i1]

                let c = cmp.Compare(ka, kb)
                if c <= 0 then
                    src.[i0] <- KeyValuePair(ka, va)
                    src.[i1] <- KeyValuePair(kb, vb)
                else
                    src.[i0] <- KeyValuePair(kb, vb)
                    src.[i1] <- KeyValuePair(ka, va)
                    
                i0 <- i0 + 2
                i1 <- i1 + 2

            if i0 < length then
                src.[i0] <- arr.[i0]
                i0 <- i0 + 1


            // merge sorted parts of length `sortedLength`
            let mutable sortedLength = 2
            let mutable sortedLengthDbl = 4
            while sortedLengthDbl < length do
                let mutable li = 0
                let mutable ri = sortedLength

                // merge case
                while ri < length do
                    mergeSeqV cmp li ri sortedLength src dst length
                    li <- ri + sortedLength
                    ri <- li + sortedLength

                // right got empty
                while li < length do
                    dst.[li] <- src.[li]
                    li <- li + 1
                    
                // sortedLength * 2
                sortedLength <- sortedLengthDbl
                sortedLengthDbl <- sortedLengthDbl <<< 1
                // swap src and dst
                let t = dst
                dst <- src
                src <- t


            // final merge-dedup run
            let cnt = mergeSeqHandleDuplicatesV cmp 0 sortedLength sortedLength src dst length
            struct(dst, cnt)


        let sortHandleDuplicates (mutateArray : bool) (cmp : IComparer<'T>) (arr : 'T[]) (length : int) =
            if length <= 0 then
                struct(arr, 0)
            else
                let arr =
                    if mutateArray then arr
                    else arr.[0 .. length-1]
                System.Array.Sort(arr, 0, length, cmp)

                let mutable i = 1
                let mutable oi = 1
                let mutable last = arr.[0]
                while i < length do
                    let v = arr.[i]
                    let c = cmp.Compare(last, v)
                    last <- v
                    i <- i + 1
                    if c = 0 then
                        arr.[oi-1] <- v
                    else
                        arr.[oi] <- v
                        oi <- oi + 1

                struct(arr, oi)
    
    [<AbstractClass>]
    type SetNode<'T>() =
        abstract member Count : int
        abstract member Height : int

        abstract member Add : comparer : IComparer<'T> * value : 'T -> SetNode<'T>
        abstract member Remove : comparer : IComparer<'T> * key : 'T -> SetNode<'T>
        abstract member AddInPlace : comparer : IComparer<'T> * value : 'T -> SetNode<'T>
        abstract member TryRemoveV : comparer : IComparer<'T> * key : 'T -> voption<SetNode<'T>>

        abstract member Filter : predicate : ('T -> bool) -> SetNode<'T>

        abstract member UnsafeRemoveHeadV : unit -> struct('T * SetNode<'T>)
        abstract member UnsafeRemoveTailV : unit -> struct(SetNode<'T> * 'T)

        abstract member SplitV : comparer : IComparer<'T> * value : 'T -> struct(SetNode<'T> * SetNode<'T> * bool)
        
    and [<Sealed>]
        SetEmpty<'T> private() =
        inherit SetNode<'T>()

        static let instance = SetEmpty<'T>() :> SetNode<'T>

        static member Instance : SetNode<'T> = instance

        override x.Count = 0
        override x.Height = 0
        override x.Add(_, value) =
            SetLeaf(value) :> SetNode<'T>
            
        override x.AddInPlace(_, value) =
            SetLeaf(value) :> SetNode<'T>

        override x.Remove(_,_) =
            x :> SetNode<'T>
            

        override x.TryRemoveV(_,_) =
            ValueNone

        override x.Filter(_) = x :> SetNode<'T>

        override x.UnsafeRemoveHeadV() = failwith "empty"
        override x.UnsafeRemoveTailV() = failwith "empty"

        override x.SplitV(_,_) =
            (x :> SetNode<'T>, x :> SetNode<'T>, false)

    and [<Sealed>]
        SetLeaf<'T> =
        class 
            inherit SetNode<'T>
            val mutable public Value : 'T

            override x.Height =
                1

            override x.Count =
                1

            override x.Add(comparer, value) =
                let c = comparer.Compare(value, x.Value)

                if c > 0 then
                    SetInner(x, value, SetEmpty.Instance) :> SetNode<'T>
                elif c < 0 then
                    SetInner(SetEmpty.Instance, value, x) :> SetNode<'T>
                else
                    SetLeaf(value) :> SetNode<'T>
           
            override x.AddInPlace(comparer, value) =
                let c = comparer.Compare(value, x.Value)

                if c > 0 then   
                    SetInner(x, value, SetEmpty.Instance) :> SetNode<'T>
                elif c < 0 then
                    SetInner(SetEmpty.Instance, value, x) :> SetNode<'T>
                else
                    x.Value <- value
                    x :> SetNode<'T>

                
            override x.Remove(comparer, value) =
                if comparer.Compare(value, x.Value) = 0 then SetEmpty.Instance
                else x :> SetNode<'T>
                
                
            override x.TryRemoveV(comparer, value) =
                if comparer.Compare(value, x.Value) = 0 then ValueSome SetEmpty.Instance
                else ValueNone

            override x.Filter(predicate : 'T -> bool) =
                if predicate x.Value then
                    x :> SetNode<'T>
                else
                    SetEmpty.Instance

            override x.UnsafeRemoveHeadV() =
                struct(x.Value, SetEmpty<'T>.Instance)

            override x.UnsafeRemoveTailV() =
                struct(SetEmpty<'T>.Instance, x.Value)

                    
            override x.SplitV(comparer : IComparer<'T>, value : 'T) =
                let c = comparer.Compare(x.Value, value)
                if c > 0 then
                    struct(SetEmpty.Instance, x :> SetNode<'T>, false)
                elif c < 0 then
                    struct(x :> SetNode<'T>, SetEmpty.Instance, false)
                else
                    struct(SetEmpty.Instance, SetEmpty.Instance, true)
                 
            new(v : 'T) = { Value = v}
        end

    and [<Sealed>]
        SetInner<'T> =
        class 
            inherit SetNode<'T>

            val mutable public Left : SetNode<'T>
            val mutable public Right : SetNode<'T>
            val mutable public Value : 'T
            val mutable public _Count : int
            val mutable public _Height : int

            static member Create(l : SetNode<'T>, v : 'T, r : SetNode<'T>) =
                let lh = l.Height
                let rh = r.Height
                let b = rh - lh

                if lh = 0 && rh = 0 then
                    SetLeaf(v) :> SetNode<'T>
                elif b > 2 then
                    // right heavy
                    let r = r :?> SetInner<'T> // must work
                    
                    if r.Right.Height >= r.Left.Height then
                        // right right case
                        SetInner.Create(
                            SetInner.Create(l, v, r.Left),
                            r.Value,
                            r.Right
                        ) 
                    else
                        // right left case
                        match r.Left with
                        | :? SetInner<'T> as rl ->
                            //let rl = r.Left :?> SetInner<'T>
                            let t1 = l
                            let t2 = rl.Left
                            let t3 = rl.Right
                            let t4 = r.Right

                            SetInner.Create(
                                SetInner.Create(t1, v, t2),
                                rl.Value,
                                SetInner.Create(t3, r.Value, t4)
                            )
                        | _ ->
                            failwith "impossible"
                            

                elif b < -2 then   
                    let l = l :?> SetInner<'T> // must work
                    
                    if l.Left.Height >= l.Right.Height then
                        SetInner.Create(
                            l.Left,
                            l.Value,
                            SetInner.Create(l.Right, v, r)
                        )

                    else
                        match l.Right with
                        | :? SetInner<'T> as lr -> 
                            let t1 = l.Left
                            let t2 = lr.Left
                            let t3 = lr.Right
                            let t4 = r
                            SetInner.Create(
                                SetInner.Create(t1, l.Value, t2),
                                lr.Value,
                                SetInner.Create(t3, v, t4)
                            )
                        | _ ->
                            failwith "impossible"

                else
                    SetInner(l, v, r) :> SetNode<'T>

            static member Join(l : SetNode<'T>, r : SetNode<'T>) =
                if l.Height = 0 then r
                elif r.Height = 0 then l
                elif l.Height > r.Height then
                    let struct(l1, v) = l.UnsafeRemoveTailV()
                    SetInner.Create(l1, v, r)
                else
                    let struct(v, r1) = r.UnsafeRemoveHeadV()
                    SetInner.Create(l, v, r1)

            override x.Count =
                x._Count

            override x.Height =
                x._Height
            
            override x.Add(comparer : IComparer<'T>, value : 'T) =
                let c = comparer.Compare(value, x.Value)
                if c > 0 then
                    SetInner.Create(
                        x.Left, 
                        x.Value,
                        x.Right.Add(comparer, value)
                    )
                elif c < 0 then
                    SetInner.Create(
                        x.Left.Add(comparer, value), 
                        x.Value,
                        x.Right
                    )
                else
                    SetInner(
                        x.Left, 
                        value,
                        x.Right
                    ) :> SetNode<'T>

            override x.AddInPlace(comparer : IComparer<'T>, value : 'T) =
                let c = comparer.Compare(value, x.Value)
                if c > 0 then
                    x.Right <- x.Right.AddInPlace(comparer, value)

                    let bal = abs (x.Right.Height - x.Left.Height)
                    if bal < 2 then 
                        x._Height <- 1 + max x.Left.Height x.Right.Height
                        x._Count <- 1 + x.Right.Count + x.Left.Count
                        x :> SetNode<'T>
                    else 
                        SetInner.Create(
                            x.Left, 
                            x.Value,
                            x.Right
                        )
                elif c < 0 then
                    x.Left <- x.Left.AddInPlace(comparer, value)
                    
                    let bal = abs (x.Right.Height - x.Left.Height)
                    if bal < 2 then 
                        x._Height <- 1 + max x.Left.Height x.Right.Height
                        x._Count <- 1 + x.Right.Count + x.Left.Count
                        x :> SetNode<'T>
                    else
                        SetInner.Create(
                            x.Left, 
                            x.Value,
                            x.Right
                        )
                else
                    x.Value <- value
                    x :> SetNode<'T>

            override x.Remove(comparer : IComparer<'T>, value : 'T) =
                let c = comparer.Compare(value, x.Value)
                if c > 0 then
                    SetInner.Create(
                        x.Left, 
                        x.Value,
                        x.Right.Remove(comparer, value)
                    )
                elif c < 0 then
                    SetInner.Create(
                        x.Left.Remove(comparer, value), 
                        x.Value,
                        x.Right
                    )
                else
                    SetInner.Join(x.Left, x.Right)
                           
            override x.TryRemoveV(comparer : IComparer<'T>, value : 'T) =
                let c = comparer.Compare(value, x.Value)
                if c > 0 then
                    match x.Right.TryRemoveV(comparer, value) with
                    | ValueSome newRight ->
                        let newNode = 
                            SetInner.Create(
                                x.Left, 
                                x.Value,
                                newRight
                            )
                        ValueSome newNode
                    | ValueNone ->
                        ValueNone
                elif c < 0 then
                    match x.Left.TryRemoveV(comparer, value) with
                    | ValueSome newLeft ->
                        let newNode = 
                            SetInner.Create(
                                newLeft, 
                                x.Value,
                                x.Right
                            )
                        ValueSome newNode
                    | ValueNone ->
                        ValueNone
                else
                    ValueSome(SetInner.Join(x.Left, x.Right))

            override x.Filter(predicate : 'T -> bool) =
                let l = x.Left.Filter(predicate)
                let self = predicate x.Value
                let r = x.Right.Filter(predicate)

                if self then
                    SetInner.Create(l, x.Value, r)
                else
                    SetInner.Join(l, r)

            override x.UnsafeRemoveHeadV() =
                if x.Left.Count = 0 then
                    struct(x.Value, x.Right)
                else
                    let struct(v,l1) = x.Left.UnsafeRemoveHeadV()
                    struct(v, SetInner.Create(l1, x.Value, x.Right))

            override x.UnsafeRemoveTailV() =   
                if x.Right.Count = 0 then
                    struct(x.Left, x.Value)
                else
                    let struct(r1,v) = x.Right.UnsafeRemoveTailV()
                    struct(SetInner.Create(x.Left, x.Value, r1), v)
                  
                    
            override x.SplitV(comparer : IComparer<'T>, value : 'T) =
                let c = comparer.Compare(value, x.Value)
                if c > 0 then
                    let struct(rl, rr, rv) = x.Right.SplitV(comparer, value)
                    struct(SetInner.Create(x.Left, x.Value, rl), rr, rv)
                elif c < 0 then
                    let struct(ll, lr, lv) = x.Left.SplitV(comparer, value)
                    struct(ll, SetInner.Create(lr, x.Value, x.Right), lv)
                else
                    struct(x.Left, x.Right, true)

            new(l : SetNode<'T>, v : 'T, r : SetNode<'T>) =
                assert(l.Count > 0 || r.Count > 0)      // not both empty
                assert(abs (r.Height - l.Height) <= 2)  // balanced
                {
                    Left = l
                    Right = r
                    Value = v
                    _Count = 1 + l.Count + r.Count
                    _Height = 1 + max l.Height r.Height
                }
        end

    let inline combineHash (a: int) (b: int) =
        uint32 a ^^^ uint32 b + 0x9e3779b9u + ((uint32 a) <<< 6) + ((uint32 a) >>> 2) |> int

    let hash (n : SetNode<'T>) =
        let rec hash (acc : int) (n : SetNode<'T>) =    
            match n with
            | :? SetLeaf<'T> as n ->
                combineHash acc (Unchecked.hash n.Value)

            | :? SetInner<'T> as n ->
                let acc = hash acc n.Left
                let acc = combineHash acc (Unchecked.hash n.Value)
                hash acc n.Right
            | _ ->
                acc

        hash 0 n

    let rec equals (cmp : IComparer<'T>) (l : SetNode<'T>) (r : SetNode<'T>) =
        if l.Count <> r.Count then
            false
        else
            // counts identical
            match l with
            | :? SetLeaf<'T> as l ->
                let r = r :?> SetLeaf<'T> // has to hold (r.Count = 1)
                cmp.Compare(l.Value, r.Value) = 0

            | :? SetInner<'T> as l ->
                match r with
                | :? SetInner<'T> as r ->
                    let struct(ll, lr, lv) = l.SplitV(cmp, r.Value)
                    if lv then
                        equals cmp ll r.Left &&
                        equals cmp lr r.Right
                    else
                        false
                | _ ->
                    false
            | _ ->
                true

open SetImplementation

[<DebuggerTypeProxy("Microsoft.FSharp.Collections.SetDebugView`1")>]
[<DebuggerDisplay("Count = {Count}")>]
[<CompiledName("FSharpSet`1")>]
[<Sealed>]
type Set<[<EqualityConditionalOn>] 'T when 'T : comparison> internal(comparer : IComparer<'T>, root : SetNode<'T>) =
        
    static let defaultComparer = LanguagePrimitives.FastGenericComparer<'T>
    static let empty = Set<'T>(defaultComparer, SetEmpty.Instance)

    [<NonSerialized>]
    // This type is logically immutable. This field is only mutated during deserialization.
    let mutable comparer = comparer
    
    [<NonSerialized>]
    // This type is logically immutable. This field is only mutated during deserialization.
    let mutable root = root

    // WARNING: The compiled name of this field may never be changed because it is part of the logical
    // WARNING: permanent serialization format for this type.
    let mutable serializedData = null

    static let toArray(root : SetNode<'T>) =
        let arr = Array.zeroCreate root.Count
        let rec copyTo (arr : array<_>) (index : int) (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let i = copyTo arr index n.Left
                arr.[i] <- n.Value
                
                copyTo arr (i+1) n.Right
            | :? SetLeaf<'T> as n ->
                arr.[index] <- n.Value
                index + 1
            | _ ->
                index

        copyTo arr 0 root |> ignore<int>
        arr

    static let fromArray (elements : 'T[]) =
        let cmp = defaultComparer
        match elements.Length with
        | 0 -> 
            SetEmpty.Instance
        | 1 ->
            let v = elements.[0]
            SetLeaf(v) :> SetNode<'T>
        | 2 -> 
            let v0 = elements.[0]
            let v1 = elements.[1]
            let c = cmp.Compare(v0, v1)
            if c > 0 then SetInner(SetEmpty.Instance, v1, SetLeaf(v0)) :> SetNode<'T>
            elif c < 0 then SetInner(SetLeaf(v0), v1, SetEmpty.Instance) :> SetNode<'T>
            else SetLeaf(v1):> SetNode<'T>
        | 3 ->
            let v0 = elements.[0]
            let v1 = elements.[1]
            let v2 = elements.[2]
            SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2)
        | 4 ->
            let v0 = elements.[0]
            let v1 = elements.[1]
            let v2 = elements.[2]
            let v3 = elements.[3]
            SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2).AddInPlace(cmp, v3)
        | 5 ->
            let v0 = elements.[0]
            let v1 = elements.[1]
            let v2 = elements.[2]
            let v3 = elements.[3]
            let v4 = elements.[4]
            SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2).AddInPlace(cmp, v3).AddInPlace(cmp, v4)
        | _ ->
            let struct(arr, len) = Sorting.sortHandleDuplicates false cmp elements elements.Length
            Set.CreateRoot(arr, len)

    [<System.Runtime.Serialization.OnSerializingAttribute>]
    member __.OnSerializing(context: System.Runtime.Serialization.StreamingContext) =
        ignore context
        serializedData <- toArray root

    [<System.Runtime.Serialization.OnDeserializedAttribute>]
    member __.OnDeserialized(context: System.Runtime.Serialization.StreamingContext) =
        ignore context
        comparer <- defaultComparer
        serializedData <- null
        root <- serializedData |> fromArray 

    static member Empty = empty

    static member Singleton(value : 'T) =
        Set<'T>(defaultComparer, SetLeaf value)

    static member private CreateTree(cmp : IComparer<'T>, arr : 'T[], cnt : int)=
        let rec create (arr : 'T[]) (l : int) (r : int) =
            if l = r then
                let v = arr.[l]
                SetLeaf(v) :> SetNode<'T>
            elif l > r then
                SetEmpty.Instance
            else
                let m = (l+r)/2
                let v = arr.[m]
                SetInner(
                    create arr l (m-1),
                    v,
                    create arr (m+1) r
                ) :> SetNode<'T>

        Set(cmp, create arr 0 (cnt-1))
  
    static member private CreateRoot(arr : 'T[], cnt : int)=
        let rec create (arr : 'T[]) (l : int) (r : int) =
            if l = r then
                let v = arr.[l]
                SetLeaf(v) :> SetNode<'T>
            elif l > r then
                SetEmpty.Instance
            else
                let m = (l+r)/2
                let v = arr.[m]
                SetInner(
                    create arr l (m-1),
                    v,
                    create arr (m+1) r
                ) :> SetNode<'T>

        create arr 0 (cnt-1)

    static member FromArray (elements : array<'T>) =
        let cmp = defaultComparer
        match elements.Length with
        | 0 -> 
            Set(cmp, SetEmpty.Instance)
        | 1 ->
            let v = elements.[0]
            Set(cmp, SetLeaf(v))
        | 2 -> 
            let v0 = elements.[0]
            let v1 = elements.[1]
            let c = cmp.Compare(v0, v1)
            if c > 0 then Set(cmp, SetInner(SetEmpty.Instance, v1, SetLeaf(v0)))
            elif c < 0 then Set(cmp, SetInner(SetLeaf(v0), v1, SetEmpty.Instance))
            else Set(cmp, SetLeaf(v1))
        | 3 ->
            let v0 = elements.[0]
            let v1 = elements.[1]
            let v2 = elements.[2]
            Set(cmp, SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2))
        | 4 ->
            let v0 = elements.[0]
            let v1 = elements.[1]
            let v2 = elements.[2]
            let v3 = elements.[3]
            Set(cmp, SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2).AddInPlace(cmp, v3))
        | 5 ->
            let v0 = elements.[0]
            let v1 = elements.[1]
            let v2 = elements.[2]
            let v3 = elements.[3]
            let v4 = elements.[4]
            Set(cmp, SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2).AddInPlace(cmp, v3).AddInPlace(cmp, v4))
        | _ ->
            let struct(arr, len) = Sorting.sortHandleDuplicates false cmp elements elements.Length
            Set.CreateTree(cmp, arr, len)
        
    static member FromList (elements : list<'T>) =
        let cmp = defaultComparer
        match elements with
        | [] -> 
            // cnt = 0
            Set(cmp, SetEmpty.Instance)

        | v0 :: rest ->
            // cnt >= 1
            match rest with
            | [] -> 
                // cnt = 1
                Set(cmp, SetLeaf(v0))
            | v1 :: rest ->
                // cnt >= 2
                match rest with
                | [] ->
                    // cnt = 2
                    let c = cmp.Compare(v0, v1)
                    if c < 0 then Set(cmp, SetInner(SetLeaf(v0), v1, SetEmpty.Instance))
                    elif c > 0 then Set(cmp, SetInner(SetEmpty.Instance, v1, SetLeaf(v0)))
                    else Set(cmp, SetLeaf(v1))
                | v2 :: rest ->
                    // cnt >= 3
                    match rest with
                    | [] ->
                        // cnt = 3
                        Set(cmp, SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2))
                    | v3 :: rest ->
                        // cnt >= 4
                        match rest with
                        | [] ->
                            // cnt = 4
                            Set(cmp, SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2).AddInPlace(cmp, v3))
                        | v4 :: rest ->
                            // cnt >= 5
                            match rest with
                            | [] ->
                                // cnt = 5
                                Set(cmp, SetLeaf(v0).AddInPlace(cmp, v1).AddInPlace(cmp, v2).AddInPlace(cmp, v3).AddInPlace(cmp, v4))
                            | v5 :: rest ->
                                // cnt >= 6
                                let mutable arr = Array.zeroCreate 16
                                let mutable cnt = 6
                                arr.[0] <- v0
                                arr.[1] <- v1
                                arr.[2] <- v2
                                arr.[3] <- v3
                                arr.[4] <- v4
                                arr.[5] <- v5
                                for t in rest do
                                    if cnt >= arr.Length then System.Array.Resize(&arr, arr.Length <<< 1)
                                    arr.[cnt] <- t
                                    cnt <- cnt + 1
                                    
                                let struct(arr1, cnt1) = Sorting.sortHandleDuplicates true cmp arr cnt
                                Set.CreateTree(cmp, arr1, cnt1)

    static member FromSeq (elements : seq<'T>) =
        match elements with
        | :? array<'T> as e -> Set.FromArray e
        | :? list<'T> as e -> Set.FromList e
        | _ ->
            let cmp = defaultComparer
            use e = elements.GetEnumerator()
            if e.MoveNext() then
                // cnt >= 1
                let t0 = e.Current
                if e.MoveNext() then
                    // cnt >= 2
                    let t1 = e.Current
                    if e.MoveNext() then
                        // cnt >= 3 
                        let t2 = e.Current
                        if e.MoveNext() then
                            // cnt >= 4
                            let t3 = e.Current
                            if e.MoveNext() then
                                // cnt >= 5
                                let t4 = e.Current
                                if e.MoveNext() then
                                    // cnt >= 6
                                    let mutable arr = Array.zeroCreate 16
                                    let mutable cnt = 6
                                    arr.[0] <- t0
                                    arr.[1] <- t1
                                    arr.[2] <- t2
                                    arr.[3] <- t3
                                    arr.[4] <- t4
                                    arr.[5] <- e.Current

                                    while e.MoveNext() do
                                        if cnt >= arr.Length then System.Array.Resize(&arr, arr.Length <<< 1)
                                        arr.[cnt] <- e.Current
                                        cnt <- cnt + 1

                                    let struct(arr1, cnt1) = Sorting.sortHandleDuplicates true cmp arr cnt
                                    Set.CreateTree(cmp, arr1, cnt1)

                                else
                                    // cnt = 5
                                    Set(cmp, SetLeaf(t0).AddInPlace(cmp, t1).AddInPlace(cmp, t2).AddInPlace(cmp, t3).AddInPlace(cmp, t4))

                            else
                                // cnt = 4
                                Set(cmp, SetLeaf(t0).AddInPlace(cmp, t1).AddInPlace(cmp, t2).AddInPlace(cmp, t3))
                        else
                            Set(cmp, SetLeaf(t0).AddInPlace(cmp, t1).AddInPlace(cmp, t2))
                    else
                        // cnt = 2
                        let c = cmp.Compare(t0, t1)
                        if c < 0 then Set(cmp, SetInner(SetLeaf(t0), t1, SetEmpty.Instance))
                        elif c > 0 then Set(cmp, SetInner(SetEmpty.Instance, t1, SetLeaf(t0)))
                        else Set(cmp, SetLeaf(t1))
                else
                    // cnt = 1
                    Set(cmp, SetLeaf(t0))

            else
                Set(cmp, SetEmpty.Instance)

    static member Union(l : Set<'T>, r : Set<'T>) =
        let rec union (cmp : IComparer<'T>) (l : SetNode<'T>) (r : SetNode<'T>) =
            match l with
            | :? SetEmpty<'T> ->  
                r
            | :? SetLeaf<'T> as l ->
                r.Add(cmp, l.Value)
            | :? SetInner<'T> as l ->
                match r with
                | :? SetEmpty<'T> ->
                    l :> SetNode<'T>
                | :? SetLeaf<'T> as r ->
                    l.Add(cmp, r.Value)
                | :? SetInner<'T> as r ->
                    if l.Count > r.Count then
                        let struct(rl, rr, _rv) = r.SplitV(cmp, l.Value)
                        SetInner.Create(
                            union cmp l.Left rl, 
                            l.Value, 
                            union cmp l.Right rr
                        )
                    else
                        let struct(ll, lr, _lv) = l.SplitV(cmp, r.Value)
                        SetInner.Create(
                            union cmp ll r.Left, 
                            r.Value, 
                            union cmp lr r.Right
                        ) 
                | _ ->
                    failwith "unexpected node"
            | _ ->
                failwith "unexpected node"

        let cmp = defaultComparer
        Set(cmp, union cmp l.Root r.Root)
        
    static member Intersect(l : Set<'T>, r : Set<'T>) =
        let rec contains (cmp : IComparer<_>) value (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let c = cmp.Compare(value, n.Value)
                if c > 0 then contains cmp value n.Right
                elif c < 0 then contains cmp value n.Left
                else true
            | :? SetLeaf<'T> as n ->
                let c = cmp.Compare(value, n.Value)
                if c = 0 then true
                else false

            | _ ->
                false

        let rec intersect (cmp : IComparer<'T>) (l : SetNode<'T>) (r : SetNode<'T>) =
            match l with
            | :? SetEmpty<'T> ->  
                SetEmpty.Instance
            | :? SetLeaf<'T> as l ->
                if contains cmp l.Value r then l :> SetNode<_>
                else SetEmpty.Instance
            | :? SetInner<'T> as l ->
                match r with
                | :? SetEmpty<'T> ->
                    SetEmpty.Instance
                | :? SetLeaf<'T> as r ->
                    if contains cmp r.Value l then r :> SetNode<_>
                    else SetEmpty.Instance
                | :? SetInner<'T> as r ->
                    if l.Count > r.Count then
                        let struct(rl, rr, rv) = r.SplitV(cmp, l.Value)
                        if rv then 
                            SetInner.Create(
                                intersect cmp l.Left rl, 
                                l.Value, 
                                intersect cmp l.Right rr
                            )
                        else
                            SetInner.Join(
                                intersect cmp l.Left rl, 
                                intersect cmp l.Right rr
                            )

                    else
                        let struct(ll, lr, lv) = l.SplitV(cmp, r.Value)
                        if lv then
                            SetInner.Create(
                                intersect cmp ll r.Left, 
                                r.Value, 
                                intersect cmp lr r.Right
                            ) 
                        else     
                            SetInner.Join(
                                intersect cmp ll r.Left, 
                                intersect cmp lr r.Right
                            ) 
                | _ ->
                    failwith "unexpected node"
            | _ ->
                failwith "unexpected node"

        let cmp = defaultComparer
        Set(cmp, intersect cmp l.Root r.Root)

    static member Difference(l : Set<'T>, r : Set<'T>) =
        let rec contains (cmp : IComparer<_>) value (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let c = cmp.Compare(value, n.Value)
                if c > 0 then contains cmp value n.Right
                elif c < 0 then contains cmp value n.Left
                else true
            | :? SetLeaf<'T> as n ->
                let c = cmp.Compare(value, n.Value)
                if c = 0 then true
                else false

            | _ ->
                false

        let rec difference (cmp : IComparer<'T>) (l : SetNode<'T>) (r : SetNode<'T>) =
            match r with
            | :? SetLeaf<'T> as r ->
                match l.TryRemoveV(cmp, r.Value) with
                | ValueSome n -> n
                | ValueNone -> l
                
            | :? SetInner<'T> as r ->
                match l with
                | :? SetLeaf<'T> as l ->
                    if contains cmp l.Value r then SetEmpty.Instance
                    else l :> SetNode<_>
                | :? SetInner<'T> as l ->
                    if l.Height > r.Height then
                        let struct(ll, lr, _lv) = l.SplitV(cmp, r.Value)

                        SetInner.Join(
                            difference cmp ll r.Left,
                            difference cmp lr r.Right
                        )
                    else
                        let struct(rl, rr, rv) = r.SplitV(cmp, l.Value)
                        if rv then
                            SetInner.Join(
                                difference cmp l.Left rl,
                                difference cmp l.Right rr
                            )
                        else
                            SetInner.Create(
                                difference cmp l.Left rl,
                                l.Value,
                                difference cmp l.Right rr
                            )

                | _ ->
                    SetEmpty.Instance

            | _ ->
                l // empty

        let cmp = defaultComparer
        Set(cmp, difference cmp l.Root r.Root)

    member x.Count = root.Count
    member x.IsEmpty = root.Count = 0
    member x.Root = root

    member x.Add(value : 'T) =
        Set(comparer, root.Add(comparer, value))
          
    member x.Remove(value : 'T) =
        Set(comparer, root.Remove(comparer, value))
        
    member x.Iter(action : 'T -> unit) =
        let rec iter (action : 'T -> unit) (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                iter action n.Left
                action n.Value
                iter action n.Right
            | :? SetLeaf<'T> as n ->
                action n.Value
            | _ ->
                ()
        iter action root

    member x.Filter(predicate : 'T -> bool) =
        Set(comparer, root.Filter(predicate))

    member x.Map(mapping : 'T -> 'U) =
        let rec run (mapping : 'T -> 'U) (cmp : IComparer<'U>) (res : SetNode<'U>) (node : SetNode<'T>) =
            match node with
            | :? SetLeaf<'T> as n ->
                let r = mapping n.Value
                res.AddInPlace(cmp, r)
            | :? SetInner<'T> as n ->
                let res1 = run mapping cmp res n.Left
                let res2 = res1.AddInPlace(cmp, mapping n.Value)
                run mapping cmp res2 n.Right
            | _ ->
                res
        let cmp = LanguagePrimitives.FastGenericComparer
        Set<'U>(cmp, run mapping cmp SetEmpty.Instance root)

    member x.Exists(predicate : 'T -> bool) =
        let rec exists (predicate : 'T -> bool) (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                exists predicate n.Left ||
                predicate n.Value ||
                exists predicate n.Right
            | :? SetLeaf<'T> as n ->
                predicate n.Value
            | _ ->
                false
        exists predicate root
        
    member x.Forall(predicate : 'T -> bool) =
        let rec forall (predicate : 'T -> bool) (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                forall predicate n.Left &&
                predicate n.Value &&
                forall predicate n.Right
            | :? SetLeaf<'T> as n ->
                predicate n.Value
            | _ ->
                true
        forall predicate root

    member x.Fold(folder : 'State -> 'T -> 'State, seed : 'State) =
        let folder = OptimizedClosures.FSharpFunc<_,_,_>.Adapt folder

        let rec fold (folder : OptimizedClosures.FSharpFunc<_,_,_>) seed (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let s1 = fold folder seed n.Left
                let s2 = folder.Invoke(s1, n.Value)
                fold folder s2 n.Right
            | :? SetLeaf<'T> as n ->
                folder.Invoke(seed, n.Value)
            | _ ->
                seed

        fold folder seed root
        
    member x.FoldBack(folder : 'T -> 'State -> 'State, seed : 'State) =
        let folder = OptimizedClosures.FSharpFunc<_,_,_>.Adapt folder

        let rec foldBack (folder : OptimizedClosures.FSharpFunc<_,_,_>) seed (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let s1 = foldBack folder seed n.Right
                let s2 = folder.Invoke(n.Value, s1)
                foldBack folder s2 n.Left
            | :? SetLeaf<'T> as n ->
                folder.Invoke(n.Value, seed)
            | _ ->
                seed

        foldBack folder seed root
        
    member x.TryPick(mapping : 'T -> option<'U>) =
        let rec run (mapping : 'T -> option<'U>) (node : SetNode<'T>) =
            match node with
            | :? SetLeaf<'T> as l ->
                mapping l.Value
                
            | :? SetInner<'T> as n ->
                match run mapping n.Left with
                | None ->
                    match mapping n.Value with
                    | Some _ as res -> res
                    | None -> run mapping n.Right
                | res -> 
                    res
            | _ ->
                None
        run mapping root

    member x.Pick(mapping : 'T -> option<'U>) =
        match x.TryPick mapping with
        | Some v -> v
        | None -> raise <| KeyNotFoundException()

    member x.Partition(predicate : 'T -> bool) =

        let cnt = x.Count 
        let a0 = Array.zeroCreate cnt
        let a1 = Array.zeroCreate cnt
        x.CopyTo(a0, 0)

        let mutable i1 = 0
        let mutable i0 = 0
        for i in 0 .. cnt - 1 do
            let v = a0.[i]
            if predicate v then 
                a0.[i0] <- v
                i0 <- i0 + 1
            else
                a1.[i1] <- v
                i1 <- i1 + 1

        Set.CreateTree(comparer, a0, i0), Set.CreateTree(comparer, a1, i1)

    member x.Contains(value : 'T) =
        let rec contains (cmp : IComparer<_>) value (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let c = cmp.Compare(value, n.Value)
                if c > 0 then contains cmp value n.Right
                elif c < 0 then contains cmp value n.Left
                else true
            | :? SetLeaf<'T> as n ->
                let c = cmp.Compare(value, n.Value)
                if c = 0 then true
                else false

            | _ ->
                false
        contains comparer value root

    member x.MinimumElement =
        let rec run (node : SetNode<_>) =
            match node with
            | :? SetLeaf<'T> as l -> l.Value
            | :? SetInner<'T> as n ->
                if n.Left.Count = 0 then n.Value
                else run n.Left
            | _ -> raise <| KeyNotFoundException()
        run root
        
    member x.MaximumElement =
        let rec run (node : SetNode<_>) =
            match node with
            | :? SetLeaf<'T> as l -> l.Value
            | :? SetInner<'T> as n ->
                if n.Right.Count = 0 then n.Value
                else run n.Right
            | _ -> raise <| KeyNotFoundException()
        run root

    member x.GetEnumerator() = new SetEnumerator<_>(root)

    member x.ToList() = 
        let rec toList acc (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                toList (n.Value :: toList acc n.Right) n.Left
            | :? SetLeaf<'T> as n ->
                n.Value :: acc
            | _ ->
                acc
        toList [] root

    member x.ToArray() =
        let arr = Array.zeroCreate x.Count
        let rec copyTo (arr : array<_>) (index : int) (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let index = copyTo arr index n.Left
                arr.[index] <- n.Value
                copyTo arr (index + 1) n.Right
            | :? SetLeaf<'T> as n ->
                arr.[index] <- n.Value
                index + 1
            | _ ->
                index

        copyTo arr 0 root |> ignore<int>
        arr

    member x.CopyTo(array : 'T[], startIndex : int) =
        if startIndex < 0 || startIndex + x.Count > array.Length then raise <| System.IndexOutOfRangeException("Map.CopyTo")
        let rec copyTo (arr : array<_>) (index : int) (n : SetNode<'T>) =
            match n with
            | :? SetInner<'T> as n ->
                let index = copyTo arr index n.Left
                arr.[index] <- n.Value
                copyTo arr (index + 1) n.Right
            | :? SetLeaf<'T> as n ->
                arr.[index] <- n.Value
                index + 1
            | _ ->
                index
        copyTo array startIndex root |> ignore<int>

    member x.CompareTo(other : Set<'T>) =
        let mutable le = x.GetEnumerator()
        let mutable re = other.GetEnumerator()

        let mutable result = 0 
        let mutable run = true
        while run do
            if le.MoveNext() then
                if re.MoveNext() then
                    let c = comparer.Compare(le.Current, re.Current)
                    if c <> 0 then 
                        result <- c
                        run <- false
                else
                    result <- 1
                    run <- false
            elif re.MoveNext() then
                result <- -1
                run <- false
            else
                run <- false
        result

    member x.IsProperSubsetOf (other : ICollection<'T>) =
        other.Count > x.Count &&
        x.Forall (fun v -> other.Contains v)
        
    member x.IsProperSubsetOf (otherSet : Set<'T>) =
        otherSet.Count > x.Count &&
        x.Forall (fun v -> otherSet.Contains v)
        
    member x.IsProperSupersetOf (otherSet : Set<'T>) =
        otherSet.Count < x.Count &&
        otherSet.Forall (fun v -> x.Contains v)
        
    member x.IsSubsetOf (other : ICollection<'T>) =
        other.Count >= x.Count &&
        x.Forall (fun v -> other.Contains v)
        
    member x.IsSubsetOf (otherSet : Set<'T>) =
        otherSet.Count >= x.Count &&
        x.Forall (fun v -> otherSet.Contains v)
        
    member x.IsSupersetOf (otherSet : Set<'T>) =
        otherSet.Count <= x.Count &&
        otherSet.Forall (fun v -> x.Contains v)

    member x.SetEquals (other : ICollection<'T>) =
        other.Count = x.Count &&
        x.Forall (fun v -> other.Contains v)
        
    member x.SetEquals (other : Set<'T>) =
        other.Count = x.Count &&
        x.Forall (fun v -> other.Contains v)

    member x.Overlaps (other : Set<'T>) =
        if x.Count < other.Count then x.Exists (fun v -> other.Contains v)
        else other.Exists (fun v -> x.Contains v)

    member x.IsProperSubsetOf(other : seq<'T>) =
        match other with
        | :? Set<'T> as other -> x.IsProperSubsetOf(other)
        | :? System.Collections.Generic.ICollection<'T> as other -> x.IsProperSubsetOf other
        | _ -> x.IsProperSubsetOf(Set.FromSeq other)
        
    member x.IsProperSupersetOf(other : seq<'T>) =
        match other with
        | :? Set<'T> as other -> x.IsProperSupersetOf(other)
        | _ -> x.IsProperSupersetOf(Set.FromSeq other)
        
    member x.IsSubsetOf(other : seq<'T>) =
        match other with
        | :? Set<'T> as other -> x.IsSubsetOf(other)
        | :? System.Collections.Generic.ICollection<'T> as other -> x.IsSubsetOf other
        | _ -> x.IsSubsetOf(Set.FromSeq other)
        
    member x.IsSupersetOf(other : seq<'T>) =
        match other with
        | :? Set<'T> as other -> x.IsSupersetOf(other)
        | _ -> x.IsSupersetOf(Set.FromSeq other)
        
    member x.SetEquals(other : seq<'T>) =
        match other with
        | :? Set<'T> as other -> x.SetEquals(other)
        | _ -> x.SetEquals(Set.FromSeq other)
        
    member x.Overlaps(other : seq<'T>) =
        match other with
        | :? Set<'T> as other -> x.Overlaps(other)
        | _ -> x.Overlaps(Set.FromSeq other)

    static member (+) (set1 : Set<'T>, set2 : Set<'T>) = Set.Union(set1, set2)
    static member (-) (set1 : Set<'T>, set2 : Set<'T>) = Set.Difference(set1, set2)


    override x.GetHashCode() =
        hash root

    override x.Equals o =
        match o with
        | :? Set<'T> as o -> equals comparer root o.Root
        | _ -> false

    interface System.IComparable with
        member x.CompareTo o = x.CompareTo (o :?> Set<_>)
            
    interface System.Collections.IEnumerable with
        member x.GetEnumerator() = new SetEnumerator<_>(root) :> _

    interface System.Collections.Generic.IEnumerable<'T> with
        member x.GetEnumerator() = new SetEnumerator<_>(root) :> _
        
    interface System.Collections.Generic.IReadOnlyCollection<'T> with
        member x.Count = x.Count

    interface System.Collections.Generic.ICollection<'T> with
        member x.Count = x.Count
        member x.IsReadOnly = true
        member x.Clear() = failwith "readonly"
        member x.Add(_) = failwith "readonly"
        member x.Remove(_) = failwith "readonly"
        member x.Contains(kvp : 'T) = x.Contains kvp
        member x.CopyTo(array : 'T[], startIndex : int) = x.CopyTo(array, startIndex)
            
    //interface System.Collections.Generic.ISet<'T> with
    //    member x.Add _ = failwith "readonly"
    //    member x.UnionWith _ = failwith "readonly"
    //    member x.ExceptWith _ = failwith "readonly"
    //    member x.IntersectWith _ = failwith "readonly"
    //    member x.SymmetricExceptWith _ = failwith "readonly"
    //    member x.IsProperSubsetOf o = x.IsProperSubsetOf o
    //    member x.IsProperSupersetOf o = x.IsProperSupersetOf o
    //    member x.IsSubsetOf o = x.IsSubsetOf o
    //    member x.IsSupersetOf o = x.IsSupersetOf o
    //    member x.SetEquals o = x.SetEquals o
    //    member x.Overlaps o = x.Overlaps o

    new(comparer : IComparer<'T>) = 
        Set<'T>(comparer, SetEmpty.Instance)
        
    new(elements : seq<'T>) = 
        let cmp = defaultComparer
        let arr = Seq.toArray elements
        let struct(arr, length) = Sorting.sortHandleDuplicates true cmp arr arr.Length
        Set<'T>(cmp, Set.CreateRoot(arr, length))

and [<NoComparison; NoEquality>] SetEnumerator<'T> =
    struct
        val mutable public Root : SetNode<'T>
        val mutable public Stack : list<struct(SetNode<'T> * bool)>
        val mutable public Value : 'T

        member x.Current : 'T = x.Value

        member x.Reset() =
            if x.Root.Height > 0 then
                x.Stack <- [struct(x.Root, true)]
                x.Value <- Unchecked.defaultof<_>

        member x.Dispose() =
            x.Root <- SetEmpty.Instance
            x.Stack <- []
            x.Value <- Unchecked.defaultof<_>
                
        member inline private x.MoveNext(deep : bool, top : SetNode<'T>) =
            let mutable top = top
            let mutable run = true

            while run do
                match top with
                | :? SetLeaf<'T> as n ->
                    x.Value <- n.Value
                    run <- false

                | :? SetInner<'T> as n ->
                    if deep then
                        if n.Left.Height = 0 then
                            if n.Right.Height > 0 then x.Stack <- struct(n.Right, true) :: x.Stack
                            x.Value <- n.Value
                            run <- false
                        else
                            if n.Right.Height > 0 then x.Stack <- struct(n.Right, true) :: x.Stack
                            x.Stack <- struct(n :> SetNode<'T>, false) :: x.Stack
                            top <- n.Left
                    else    
                        x.Value <- n.Value
                        run <- false

                | _ ->
                    failwith "empty node"
    
            
        member x.MoveNext() : bool =
            match x.Stack with
            | struct(n, deep) :: rest ->
                x.Stack <- rest
                x.MoveNext(deep, n)
                true
            | [] ->
                false
                            
            
        interface System.Collections.IEnumerator with
            member x.MoveNext() = x.MoveNext()
            member x.Reset() = x.Reset()
            member x.Current = x.Current :> obj

        interface System.Collections.Generic.IEnumerator<'T> with
            member x.Dispose() = x.Dispose()
            member x.Current = x.Current



        new(r : SetNode<'T>) =
            if r.Height = 0 then
                { 
                    Root = r
                    Stack = []
                    Value = Unchecked.defaultof<_>
                }
            else       
                { 
                    Root = r
                    Stack = [struct(r, true)]
                    Value = Unchecked.defaultof<_>
                }

    end

and internal SetDebugView<'T when 'T : comparison> =

    [<DebuggerBrowsable(DebuggerBrowsableState.RootHidden)>]
    val mutable public Entries : 'T[]

    new(m : Set<'T>) =
        {
            Entries = Seq.toArray (Seq.truncate 10000 m)
        }
       
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix); RequireQualifiedAccess>]
module Set =

    [<GeneralizableValue; CompiledName("Empty")>]
    let empty<'T when 'T : comparison> = Set<'T>.Empty
    
    [<CompiledName("Singleton")>]
    let singleton (value : 'T) = Set<'T>.Singleton value

    [<CompiledName("IsEmpty")>]
    let isEmpty (set : Set<'T>) = set.Count <= 0
    
    [<CompiledName("Count")>]
    let count (set : Set<'T>) = set.Count
    
    [<CompiledName("Add")>]
    let add (value : 'T) (set : Set<'T>) = set.Add(value)
    
    [<CompiledName("Remove")>]
    let remove (value : 'T) (set : Set<'T>) = set.Remove(value)

    [<CompiledName("Contains")>]
    let contains (element : 'T) (set : Set<'T>) = set.Contains(element)
    
    [<CompiledName("MinElement")>]
    let minElement (set : Set<'T>) = set.MinimumElement
    
    [<CompiledName("MaxElement")>]
    let maxElement (set : Set<'T>) = set.MaximumElement

    [<CompiledName("Iterate")>]
    let iter (action : 'T -> unit) (set : Set<'T>) = set.Iter(action)
    
    [<CompiledName("Filter")>]
    let filter (predicate : 'T -> bool) (set : Set<'T>) = set.Filter(predicate)
    
    [<CompiledName("Map")>]
    let map (mapping : 'T -> 'U) (set : Set<'T>) = set.Map(mapping)

    [<CompiledName("Exists")>]
    let exists (predicate : 'T -> bool) (set : Set<'T>) = set.Exists(predicate)
    
    [<CompiledName("ForAll")>]
    let forall (predicate : 'T -> bool) (set : Set<'T>) = set.Forall(predicate)

    [<CompiledName("Fold")>]
    let fold<'T,'State when 'T : comparison> (folder : 'State -> 'T -> 'State) (state : 'State) (set : Set<'T>) : 'State = 
        set.Fold(folder, state)
    
    [<CompiledName("FoldBack")>]
    let foldBack (folder : 'T -> 'State -> 'State) (set : Set<'T>) (state : 'State) = 
        set.FoldBack(folder, state)

    [<CompiledName("OfSeq")>]
    let ofSeq (elements : seq<'T>) = Set.FromSeq elements
    
    [<CompiledName("OfList")>]
    let ofList (elements : list<'T>) = Set.FromList elements
    
    [<CompiledName("OfArray")>]
    let ofArray (array : 'T[]) = Set.FromArray array
    
    [<CompiledName("ToSeq")>]
    let toSeq (set : Set<'T>) = set :> seq<_>

    [<CompiledName("ToList")>]
    let toList (set : Set<'T>) = set.ToList()
    
    [<CompiledName("ToArray")>]
    let toArray (set : Set<'T>) = set.ToArray()
    
    [<CompiledName("IsSuperset")>]
    let isSuperset (set1 : Set<'T>) (set2 : Set<'T>) = set1.IsSupersetOf set2
    
    [<CompiledName("IsSubset")>]
    let isSubset (set1 : Set<'T>) (set2 : Set<'T>) = set1.IsSubsetOf set2
    
    [<CompiledName("IsProperSuperset")>]
    let isProperSuperset (set1 : Set<'T>) (set2 : Set<'T>) = set1.IsProperSupersetOf set2
    
    [<CompiledName("IsProperSubset")>]
    let isProperSubset (set1 : Set<'T>) (set2 : Set<'T>) = set1.IsProperSubsetOf set2

    [<CompiledName("Union")>]
    let union (set1 : Set<'T>) (set2 : Set<'T>) = Set.Union(set1, set2)
    
    [<CompiledName("Intersect")>]
    let intersect (set1 : Set<'T>) (set2 : Set<'T>) = Set.Intersect(set1, set2)
    
    [<CompiledName("Difference")>]
    let difference (set1 : Set<'T>) (set2 : Set<'T>) = Set.Difference(set1, set2)
    
    [<CompiledName("UnionMany")>]
    let unionMany (sets : seq<Set<'T>>) =
        use e = (sets :> seq<_>).GetEnumerator()
        if e.MoveNext() then
            let mutable m = e.Current
            while e.MoveNext() do
                m <- union m e.Current
            m
        else
            empty
            
    [<CompiledName("IntersectMany")>]
    let intersectMany (sets : seq<Set<'T>>) =
        use e = (sets :> seq<_>).GetEnumerator()
        if e.MoveNext() then
            let mutable m = e.Current
            while e.MoveNext() do
                m <- intersect m e.Current
            m
        else
            empty

    [<CompiledName("TryPick")>]
    let tryPick (mapping : 'T -> option<'U>) (set : Set<'T>) =
        set.TryPick(mapping)

    [<CompiledName("Pick")>]
    let pick (mapping : 'T -> option<'U>) (set : Set<'T>) =
        set.Pick(mapping)

    [<CompiledName("Partition")>]
    let partition (predicate : 'T -> bool) (set : Set<'T>) =
        set.Partition(predicate)

