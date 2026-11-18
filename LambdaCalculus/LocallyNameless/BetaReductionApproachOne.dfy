include "LocallyNameless.dfy"
include "../BetaReduction.dfy"

function numberOfRedexes(t:RefLambdaTerm):nat 
{
    match t 
        case FreeVar(_)=> 0
        case BoundVar(_)=> 0
        case RefLambda(t')=>numberOfRedexes(t')
        case App(t1,t2) => if isRefAppLambda(t) then 1+numberOfRedexes(t1)+numberOfRedexes(t2) 
                                else numberOfRedexes(t1)+numberOfRedexes(t2)
}
lemma OpeningMaintainsNumberOfRedexes(t:RefLambdaTerm)
    ensures var (opened_t,_):=open(t);
    numberOfRedexes(t)==numberOfRedexes(opened_t)
{
    var ids:=freeVarsSeq(t);
    var new_id:=addAnUniqueId(ids)[0];
    OpeningMaintainsNumberOfRedexes'(t,new_id,0);
}
lemma OpeningMaintainsNumberOfRedexes'(t:RefLambdaTerm,new_id:Id,depth:nat)
    ensures var opened_t:=open'(depth,new_id,t);
    numberOfRedexes(t)==numberOfRedexes(opened_t)
{
    var opened_t:=open'(depth,new_id,t);
    match t 
        case FreeVar(x) =>
        {
            assert t==opened_t;
        }
        case BoundVar(ref_id) =>
        {
            if (ref_id==depth)
            {
                assert opened_t==FreeVar(new_id);
                assert numberOfRedexes(opened_t)==0;
            }
            else 
            {
                assert t==opened_t;
            }
        }
        case App(t1,t2) =>
        {
            OpeningMaintainsNumberOfRedexes'(t2,new_id,depth);
            OpeningMaintainsNumberOfRedexes'(t1,new_id,depth);

            if isRefAppLambda(t) 
            {
                assert isRefAppLambda(opened_t);
            }
        }
        case  RefLambda(t')=>
        {
            OpeningMaintainsNumberOfRedexes'(t',new_id,depth+1);
        }
}

function refBetaReduction(t:RefLambdaTerm) : RefLambdaTerm
    requires isRefAppLambda(t)
    
{
    match t 
        case App(t1,t2) => (match t1
                                case RefLambda(t1') => opening(t1',0,t2)
        )
}

function refBetaReductionStep(t:RefLambdaTerm,choice:nat):RefLambdaTerm
    requires numberOfRedexes(t)>choice 
    decreases refLHeight(t)
{
    match t 
        case App(t1,t2) => (
            var n1:=numberOfRedexes(t1);
            var n2:=numberOfRedexes(t2);
            if isRefAppLambda(t) then 
            (
                if choice==0 then 
                    refBetaReduction(t)
                else 
                    if (choice<=n1) then 
                        App(refBetaReductionStep(t1,choice-1),t2)
                    else 
                        assert choice>n1;
                        assert choice<numberOfRedexes(t);
                        assert n2+n1+1==numberOfRedexes(t); 
                        App(t1,refBetaReductionStep(t2,choice-1-n1))
            )
            else 
            (
                if (choice<n1) then 
                        App(refBetaReductionStep(t1,choice),t2)
                    else 
                        assert choice>=n1;
                        assert choice<numberOfRedexes(t);
                        assert n2+n1==numberOfRedexes(t); 
                        App(t1,refBetaReductionStep(t2,choice-n1))
            )
            )
        case RefLambda(t')=>
        (
            var (opened_t',x):=open(t');
            assert refLHeight(t')<refLHeight(t);
            assert refLHeight(t')==refLHeight(opened_t');
            OpeningMaintainsNumberOfRedexes(t');
            RefLambda(close(refBetaReductionStep(opened_t',choice),x))
        ) 

}

lemma TheCountIsTheSameNamedLambda(t:LambdaTerm,nameless_t:RefLambdaTerm)
    requires nameless_t==fromLambdaToRef(t)
    ensures numberOfPossibleReducations(t)==numberOfRedexes(nameless_t)
{
    assert nameless_t==fromLambdaToRef'(t,[]);
    TheCountIsTheSameNamedLambda'(t,nameless_t,[]);
}

lemma TheCountIsTheSameNamedLambda'(t:LambdaTerm,nameless_t:RefLambdaTerm,ids:seq<Id>)
    requires nameless_t==fromLambdaToRef'(t,ids)
    ensures numberOfPossibleReducations(t)==numberOfRedexes(nameless_t)
{
    match t 
        case Var(_) =>{
            assert numberOfPossibleReducations(t)==0;
            assert exists x:nat:: nameless_t==FreeVar(x) || nameless_t==BoundVar(x);
            assert numberOfRedexes(nameless_t)==0;
        }
        case Application(t1,t2)=>{
            var nameless_t1:=fromLambdaToRef'(t1,ids);
            var nameless_t2:=fromLambdaToRef'(t2,ids);

            TheCountIsTheSameNamedLambda'(t1,nameless_t1,ids);
            TheCountIsTheSameNamedLambda'(t2,nameless_t2,ids);

        
            if (isCorrectForBetaReduction(t))
            {
                var t':LambdaTerm,x:Id:| t1==Lambda(x,t');
                var nameless_t':=fromLambdaToRef'(t',ids);
                assert isRefAppLambda(nameless_t);
            }
        }
        case Lambda(x,t')=>{
            var nameless_t':=fromLambdaToRef'(t',ids+[x]);
            TheCountIsTheSameNamedLambda'(t',nameless_t',ids+[x]);
        }

}

lemma theCountIsTheSameRef(t:RefLambdaTerm,named_t:LambdaTerm)
    requires locallyClosed(t) 
    requires named_t==fromRefToLambda(t)
    ensures numberOfRedexes(t)==numberOfPossibleReducations(named_t)
{
    TheCountIsTheSameRef'(t,freeVarsSeq(t),[],named_t);
}

lemma TheCountIsTheSameRef'(t:RefLambdaTerm,ids:seq<Id>,lambda_names:seq<Id>,named_t:LambdaTerm)
    requires locallyClosed'(t,|lambda_names|)
    requires allUnique(ids) 
    requires forall id:Id::id in ids ==>!(id in lambda_names)
    requires allUnique(lambda_names)
    requires fromRefToLambda'(t,ids,lambda_names)==named_t
    ensures  numberOfRedexes(t)==numberOfPossibleReducations(named_t)
{
    match t 
        case RefLambda(t') =>
        {
            var new_ids:=addAnUniqueId(reunion(ids,lambda_names));
            var named_t':=fromRefToLambda'(t',ids,lambda_names+[new_ids[0]]);
            TheCountIsTheSameRef'(t',ids,lambda_names+[new_ids[0]],named_t');
        }
        case FreeVar(_)=>
        {
            assert exists x:Id::named_t==Var(x);

        }
        case BoundVar(_)=>
        {
            assert exists x:Id::named_t==Var(x);
        }
        case App(t1,t2)=>
        {
            var named_t1:=fromRefToLambda'(t1,ids,lambda_names);
            var named_t2:=fromRefToLambda'(t2,ids,lambda_names);
            TheCountIsTheSameRef'(t1,ids,lambda_names,named_t1);
            TheCountIsTheSameRef'(t2,ids,lambda_names,named_t2);
        }

}
