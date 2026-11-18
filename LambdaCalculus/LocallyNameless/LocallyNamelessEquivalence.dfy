include "LocallyNameless.dfy"
include "../BetaReduction.dfy"
include "ChurchRosser.dfy"

lemma FindIdOfPos(ids:seq<Id>, i:nat)
    requires i < |ids|
    requires allUnique(ids)
    ensures findId(ids, ids[i]) == Some(i)
{
    assert ids[i] in ids;
    var p :| findId(ids, ids[i]) == Some(p);
    assert p < |ids| && ids[p] == ids[i];
}
lemma FromRefToLambdaBackToRef(t:RefLambdaTerm,named_t:LambdaTerm,nameless_t:RefLambdaTerm)
    requires locallyClosed(t)
    requires named_t==fromRefToLambda(t)
    requires nameless_t==fromLambdaToRef(named_t)
    ensures nameless_t==t
{
    IncludesItself(freeVarsSeq(t));
    assert includes(freeVarsSeq(t),freeVarsSeq(t));
    FromRefToLambdaBackToRef'(t,named_t,freeVarsSeq(t),[],nameless_t,[]);
}

lemma FromRefToLambdaBackToRef'(t:RefLambdaTerm,
    named_t:LambdaTerm,ids1:seq<Id>,lambda_names:seq<Id>,
    nameless_t:RefLambdaTerm,ids2:seq<Id>)
    requires locallyClosed'(t,|lambda_names|)
    requires lambda_names==ids2
    requires allUnique(ids1)
    requires includes(ids1,freeVarsSeq(t))
    requires allUnique(lambda_names)
    requires forall id:Id::id in ids1 ==>!(id in lambda_names)
    requires named_t==fromRefToLambda'(t,ids1,lambda_names)
    requires nameless_t==fromLambdaToRef'(named_t,ids2)
    ensures nameless_t==t
{
    match t 
        case FreeVar(x)=>{

            assert named_t==Var(x);
            assert x in freeVarsSeq(t);
            assert x in ids1;
            assert !(x in lambda_names);
            assert !(x in ids2);
            assert findId(ids2,x)==None;
            assert nameless_t==FreeVar(x);
        }
        case BoundVar(ref)=>{
            assert named_t==Var(lambda_names[|lambda_names| - 1 - ref]);
            var x:=lambda_names[|lambda_names| - 1 - ref];
            assert findId(lambda_names,x)==Some(|lambda_names| - 1 - ref);
            assert nameless_t==BoundVar( ref);
        }
        case App(t1,t2)=>{
            var named_t1:=fromRefToLambda'(t1,ids1,lambda_names);
            var named_t2:=fromRefToLambda'(t2,ids1,lambda_names);
            assert named_t==Application(named_t1,named_t2);
            var nameless_t1:=fromLambdaToRef'(named_t1,lambda_names);
            var nameless_t2:=fromLambdaToRef'(named_t2,lambda_names);
            assert nameless_t==App(nameless_t1,nameless_t2);

            reunionIncludesBothSets(freeVarsSeq(t1),freeVarsSeq(t2));

            FromRefToLambdaBackToRef'(t1,named_t1,ids1,lambda_names
            ,nameless_t1,lambda_names);
            assert nameless_t1==t1;
            FromRefToLambdaBackToRef'(t2,named_t2,ids1,lambda_names
            ,nameless_t2,lambda_names);
            assert nameless_t2==t2;

        }
        case RefLambda(t')=>{
            var new_id:=addAnUniqueId(reunion(ids1,lambda_names))[0];
            var new_lambda_names:=lambda_names+[new_id];
            var named_t':=fromRefToLambda'(t',ids1,new_lambda_names);
            assert named_t==Lambda(new_id,named_t');

            var nameless_t':=fromLambdaToRef'(named_t',new_lambda_names);
            assert nameless_t==RefLambda(nameless_t');
           
            FromRefToLambdaBackToRef'(t',named_t',ids1,new_lambda_names,
            nameless_t',new_lambda_names);

            assert nameless_t'==t';
        }

}

lemma FromLambdaToRefBackToLambda(t:LambdaTerm,nameless_t:RefLambdaTerm,named_t:LambdaTerm)
    requires nameless_t==fromLambdaToRef(t)
    requires locallyClosed(nameless_t)
    requires named_t==fromRefToLambda(nameless_t)
    ensures alphaEquivalence(t,named_t)
{
    IncludesItself(freeVarsSeq(nameless_t));
    assert includes(freeVarsSeq(nameless_t),freeVarsSeq(nameless_t));
    FromLambdaToRefBackToLambda'(t,nameless_t,[],named_t,freeVarsSeq(nameless_t),[]);
}

lemma FromLambdaToRefBackToLambda'(t:LambdaTerm,
    nameless_t:RefLambdaTerm,ids1:seq<Id>,
    named_t:LambdaTerm,ids2:seq<Id>,lambda_names:seq<Id>)

    requires nameless_t==fromLambdaToRef'(t,ids1)
    requires locallyClosed'(nameless_t,|lambda_names|)
    requires |ids1|==|lambda_names|
    requires allUnique(ids2)
    requires includes(ids2,freeVarsSeq(nameless_t))
    requires forall id:Id::id in ids2 ==>!(id in lambda_names)
    requires allUnique(lambda_names)
    requires named_t==fromRefToLambda'(nameless_t,ids2,lambda_names)
    ensures alphaEquivalence'(t,named_t,ids1,lambda_names)
{
    match t 
        case Var(x) =>
        {
            match findId(ids1,x)
                case None=>
                {
                    assert x in freeVarsSeq(nameless_t);
                    var j:nat :| j<|ids2| && ids2[j]==x;   
                    assert x in ids2;
                    assert !(x in lambda_names);
                    assert findId(lambda_names,x)==None;
                }
                case Some(refId)=>
                {
                    assert refId < |ids1|;                           
                    assert nameless_t == BoundVar(|ids1| - 1 - refId);
                    var n := |lambda_names|;
                    assert n == |ids1|;
                    var new_id := lambda_names[n - 1 - (|ids1| - 1 - refId)];
                    assert n - 1 - (|ids1| - 1 - refId) == refId;
                    assert named_t == Var(new_id);
                    assert new_id == lambda_names[refId];
                    FindIdOfPos(lambda_names, refId);
                    assert findId(lambda_names, new_id) == Some(refId);
                  
                }
        }
        case Lambda(x,t')=>
        {
            var new_ids1:=ids1+[x];
            var nameless_t':=fromLambdaToRef'(t',new_ids1);
            assert nameless_t==RefLambda(nameless_t');

            var new_id:=addAnUniqueId(reunion(ids2,lambda_names))[0];
            var new_lambda_names:=lambda_names+[new_id];
            var named_t':=fromRefToLambda'(nameless_t',ids2,new_lambda_names);

            FromLambdaToRefBackToLambda'(t',nameless_t',new_ids1,named_t',ids2,new_lambda_names);
            assert alphaEquivalence'(t',named_t',new_ids1,new_lambda_names);
        }
        case Application(t1,t2)=>
        {
            var nameless_t1:=fromLambdaToRef'(t1,ids1);
            var nameless_t2:=fromLambdaToRef'(t2,ids1); 
            assert nameless_t==App(nameless_t1,nameless_t2);

            var named_t1:=fromRefToLambda'(nameless_t1,ids2,lambda_names);
            var named_t2:=fromRefToLambda'(nameless_t2,ids2,lambda_names);
            assert named_t==Application(named_t1,named_t2);

            reunionIncludesBothSets(freeVarsSeq(nameless_t1),freeVarsSeq(nameless_t2));
            FromLambdaToRefBackToLambda'(t1,nameless_t1,ids1,named_t1,ids2,lambda_names);
            FromLambdaToRefBackToLambda'(t2,nameless_t2,ids1,named_t2,ids2,lambda_names);

            assert alphaEquivalence'(t1,named_t1,ids1,lambda_names);
            assert alphaEquivalence'(t2,named_t2,ids1,lambda_names);
        }

}

