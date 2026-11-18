include "ParallelDiamond.dfy"

ghost predicate isThereAParallelPath(t1:RefLambdaTerm,t2:RefLambdaTerm)
{
   exists n:nat::isThereAParallelPath'(t1,t2,n)
}
ghost predicate isThereAParallelPath'(t1:RefLambdaTerm,t2:RefLambdaTerm,n:nat)
    decreases n 
{
    if n==0 then t1==t2
    else exists t':RefLambdaTerm::refParallelReduction(t1,t') && isThereAParallelPath'(t',t2,n-1)
}


lemma ParallelExtension(t1:RefLambdaTerm,t2:RefLambdaTerm,t2':RefLambdaTerm,n:nat)
    requires isThereAParallelPath'(t1,t2,n)
    requires refParallelReduction(t2,t2')
    decreases n
    ensures isThereAParallelPath'(t1,t2',n+1)
{
    if n==0
    {
        assert t1==t2;
        assert isThereAParallelPath'(t2',t2',0);
        assert refParallelReduction(t1,t2') && isThereAParallelPath'(t2',t2',0);
    }
    else
    {
        var t':RefLambdaTerm :| refParallelReduction(t1,t') && isThereAParallelPath'(t',t2,n-1);
        ParallelExtension(t',t2,t2',n-1);
        assert isThereAParallelPath'(t',t2',n);
        assert refParallelReduction(t1,t') && isThereAParallelPath'(t',t2',n);
    }
}

lemma ParallelPathTransitive(t1:RefLambdaTerm, t2:RefLambdaTerm, t3:RefLambdaTerm)
    requires isThereAParallelPath(t1,t2) && isThereAParallelPath(t2,t3)
    ensures  isThereAParallelPath(t1,t3)
{
    var n1:nat:|isThereAParallelPath'(t1,t2,n1);
    var n2:nat:|isThereAParallelPath'(t2,t3,n2);
    ParallelPathTransitive'(t1,t2,t3,n1,n2);
}

lemma ParallelPathTransitive'(t1:RefLambdaTerm, t2:RefLambdaTerm, t3:RefLambdaTerm,n1:nat,n2:nat)
    requires isThereAParallelPath'(t1,t2,n1) && isThereAParallelPath'(t2,t3,n2)
    decreases n2
    ensures  isThereAParallelPath'(t1,t3,n1+n2)
{
    if n2==0
    {
        assert t2==t3;
        assert isThereAParallelPath'(t1,t3,n1+0);
    }
    else 
    {
        var t2':RefLambdaTerm:|refParallelReduction(t2,t2') &&  isThereAParallelPath'(t2',t3,n2-1);
        ParallelExtension(t1,t2,t2',n1);
        assert isThereAParallelPath'(t1,t2',n1+1);
        ParallelPathTransitive'(t1,t2',t3,n1+1,n2-1);
    }
}


lemma OpeningPreservesClosed(t:RefLambdaTerm, u:RefLambdaTerm, depth:nat)
    requires locallyClosed'(t,depth+1)
    requires locallyClosed'(u,depth)
    ensures  locallyClosed'(opening(t,depth,u),depth)
{
    match t
        case FreeVar(_) => {}
        case BoundVar(ref) => {
            if ref==depth { assert opening(t,depth,u)==u; }
            else { assert ref<depth; }
        }
        case App(t1,t2) => {
            OpeningPreservesClosed(t1,u,depth);
            OpeningPreservesClosed(t2,u,depth);
        }
        case RefLambda(t1) => {
            LocallyClosedAtDifferentLevels(u,depth,depth+1);
            OpeningPreservesClosed(t1,u,depth+1);
        }
}

lemma CloseOfClosedIsBody'(t:RefLambdaTerm, x:Id, depth:nat)
    requires locallyClosed'(t,depth)
    ensures  locallyClosed'(close'(t,x,depth),depth+1)
{
    match t
        case FreeVar(y) => {}
        case BoundVar(n) => { assert n<depth; }
        case App(t1,t2) => {
            CloseOfClosedIsBody'(t1,x,depth);
            CloseOfClosedIsBody'(t2,x,depth);
        }
        case RefLambda(t1) => { CloseOfClosedIsBody'(t1,x,depth+1); }
}


ghost predicate betaRuleRedex(t1:RefLambdaTerm, t2:RefLambdaTerm)
{
    match t1
        case App(t1a,t1b) => (match t1a
            case RefLambda(t1a') => locallyClosed'(t1a',1) && locallyClosed(t1b) && t2==opening(t1a',0,t1b)
            case _ => false)
        case _ => false
}

ghost predicate betaRuleApp1(t1:RefLambdaTerm, t2:RefLambdaTerm)
    decreases refLHeight(t1), 0
{
    match t1
        case App(t1a,t1b) => (match t2
            case App(t2a,t2b) => t1b==t2b && locallyClosed(t1b) && refBeta(t1a,t2a)
            case _ => false)
        case _ => false
}

ghost predicate betaRuleApp2(t1:RefLambdaTerm, t2:RefLambdaTerm)
    decreases refLHeight(t1), 0
{
    match t1
        case App(t1a,t1b) => (match t2
            case App(t2a,t2b) => t2a==t1a && locallyClosed(t1a) && refBeta(t1b,t2b)
            case _ => false)
        case _ => false
}

ghost predicate betaRuleAbs(t1:RefLambdaTerm, t2:RefLambdaTerm)
    decreases refLHeight(t1),0 
{
    match t1
        case RefLambda(t1') =>
            assert forall x:Id:: refLHeight(open'(0,x,t1'))==refLHeight(t1');
            (match t2
                case RefLambda(t2') => (exists L:seq<Id>:: allUnique(L) &&
                    forall x:Id:: !(x in L) ==> refBeta(open'(0,x,t1'),open'(0,x,t2')))
                case _ => false)
        case _ => false
}

ghost predicate refBeta(t1:RefLambdaTerm, t2:RefLambdaTerm)
    decreases refLHeight(t1)
{
    betaRuleRedex(t1,t2) || betaRuleApp1(t1,t2) || betaRuleApp2(t1,t2) || betaRuleAbs(t1,t2)
}

ghost predicate refBetaPath'(t1:RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    decreases n
{
    if n==0 then t1==t2
    else exists t':RefLambdaTerm:: refBeta(t1,t') && refBetaPath'(t',t2,n-1)
}
ghost predicate refBetaPath(t1:RefLambdaTerm, t2:RefLambdaTerm)
{
    exists n:nat:: refBetaPath'(t1,t2,n)
}

lemma RefBetaCases(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires refBeta(t1,t2)
    ensures betaRuleRedex(t1,t2) || betaRuleApp1(t1,t2) || betaRuleApp2(t1,t2) || betaRuleAbs(t1,t2)
{}
lemma RefBetaIntro(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires betaRuleRedex(t1,t2) || betaRuleApp1(t1,t2) || betaRuleApp2(t1,t2) || betaRuleAbs(t1,t2)
    ensures refBeta(t1,t2)
{}

lemma RefBetaRegular(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires refBeta(t1,t2)
    ensures locallyClosed(t1) && locallyClosed(t2)
    decreases refLHeight(t1)
{
    RefBetaCases(t1,t2);
    match t1
        case FreeVar(_) => { assert false; }
        case BoundVar(_) => { assert false; }
        case App(a,c) => {
            if betaRuleRedex(t1,t2) {
                match a
                    case RefLambda(b) => { OpeningPreservesClosed(b,c,0); }
                    case _ => { assert false; }
            } else {
                match t2
                    case App(a',c') => {
                        if betaRuleApp1(t1,t2) { RefBetaRegular(a,a'); }
                        else { RefBetaRegular(c,c'); }
                    }
                    case _ => { assert false; }
            }
        }
        case RefLambda(b) => {
            match t2
                case RefLambda(b') => {
                    var L:seq<Id> :| allUnique(L) &&
                        forall x:Id:: !(x in L) ==> refBeta(open'(0,x,b),open'(0,x,b'));
                    var x:Id := addAnUniqueId(L)[0];
                    assert refLHeight(open'(0,x,b))==refLHeight(b);
                    RefBetaRegular(open'(0,x,b),open'(0,x,b'));
                    BodyUp(b,x);
                    BodyUp(b',x);
                }
                case _ => { assert false; }
        }
}

lemma RefBetaSubstOut(t:RefLambdaTerm, t':RefLambdaTerm, x:Id, u:RefLambdaTerm)
    requires refBeta(t,t')
    requires locallyClosed(u)
    ensures  refBeta(LNSubstitution(t,x,u),LNSubstitution(t',x,u))
    decreases refLHeight(t)
{
    RefBetaCases(t,t');
    match t
        case FreeVar(_) => { assert false; }
        case BoundVar(_) => { assert false; }
        case App(a,c) => {
            if betaRuleRedex(t,t') {
                match a
                    case RefLambda(b) => {
                        RefSubsitutionBody(b,x,u);
                        RefSubsitutionClosure(c,x,u);
                        SubstitutionOpen(b,x,u,c,0);
                        assert LNSubstitution(t,x,u)==App(RefLambda(LNSubstitution(b,x,u)),LNSubstitution(c,x,u));
                        assert betaRuleRedex(LNSubstitution(t,x,u),LNSubstitution(t',x,u));
                    }
                    case _ => { assert false; }
            } else {
                match t'
                    case App(a',c') => {
                        if betaRuleApp1(t,t') {
                            RefBetaSubstOut(a,a',x,u);
                            RefSubsitutionClosure(c,x,u);
                            assert betaRuleApp1(LNSubstitution(t,x,u),LNSubstitution(t',x,u));
                        } else {
                            RefBetaSubstOut(c,c',x,u);
                            RefSubsitutionClosure(a,x,u);
                            assert betaRuleApp2(LNSubstitution(t,x,u),LNSubstitution(t',x,u));
                        }
                    }
                    case _ => { assert false; }
            }
        }
        case RefLambda(b) => {
            match t'
                case RefLambda(b') => {
                    var L:seq<Id> :| allUnique(L) &&
                        forall y:Id:: !(y in L) ==> refBeta(open'(0,y,b),open'(0,y,b'));
                    var L2:seq<Id> := if x in L then L else L+[x];
                    assert allUnique(L2) && x in L2;
                    forall y:Id | !(y in L2)
                        ensures refBeta(open'(0,y,LNSubstitution(b,x,u)),open'(0,y,LNSubstitution(b',x,u)))
                    {
                        assert refLHeight(open'(0,y,b))==refLHeight(b);
                        RefBetaSubstOut(open'(0,y,b),open'(0,y,b'),x,u);
                        SubstitutionAndOpening(b,x,y,u,0);
                        SubstitutionAndOpening(b',x,y,u,0);
                    }
                    assert betaRuleAbs(LNSubstitution(t,x,u),LNSubstitution(t',x,u));
                }
                case _ => { assert false; }
        }
}

lemma RefBetaAbsIntro(t:RefLambdaTerm, t':RefLambdaTerm, x:Id)
    requires !(x in freeVarsSeq(t)) && !(x in freeVarsSeq(t'))
    requires refBeta(open'(0,x,t),open'(0,x,t'))
    ensures  refBeta(RefLambda(t),RefLambda(t'))
{
    forall y:Id
        ensures refBeta(open'(0,y,t),open'(0,y,t'))
    {
        RefBetaSubstOut(open'(0,x,t),open'(0,x,t'),x,FreeVar(y));
        SubstitutionIntro(t,x,FreeVar(y),0);
        SubstitutionIntro(t',x,FreeVar(y),0);
        OpeningWithFreeVarIsOpen(t,0,y);
        OpeningWithFreeVarIsOpen(t',0,y);
    }
    assert allUnique([]);
    assert betaRuleAbs(RefLambda(t),RefLambda(t'));
}

lemma OpenInjective(t:RefLambdaTerm, t':RefLambdaTerm, x:Id)
    requires !(x in freeVarsSeq(t)) && !(x in freeVarsSeq(t'))
    requires open'(0,x,t)==open'(0,x,t')
    ensures  t==t'
{
    CloseOpen(t,x);
    CloseOpen(t',x);
}


lemma CloseFreeVars(s:RefLambdaTerm, x:Id, d:nat)
    ensures !(x in freeVarsSeq(close'(s,x,d)))
{
    match s
        case FreeVar(_) => {}
        case BoundVar(_) => {}
        case RefLambda(s1) => { CloseFreeVars(s1,x,d+1); }
        case App(s1,s2) => { CloseFreeVars(s1,x,d); CloseFreeVars(s2,x,d); }
}

lemma RefBetaPathAbsIntro'(t:RefLambdaTerm, t':RefLambdaTerm, x:Id, n:nat)
    requires !(x in freeVarsSeq(t)) && !(x in freeVarsSeq(t'))
    requires refBetaPath'(open'(0,x,t),open'(0,x,t'),n)
    ensures  refBetaPath'(RefLambda(t),RefLambda(t'),n)
    decreases n
{
    if n==0 {
        OpenInjective(t,t',x);
    } else {
        var s:RefLambdaTerm :| refBeta(open'(0,x,t),s) && refBetaPath'(s,open'(0,x,t'),n-1);
        RefBetaRegular(open'(0,x,t),s);
        OpenClose(s,x);                       
        CloseOfClosedIsBody'(s,x,0);
        CloseFreeVars(s,x,0);
        var t'':=close(s,x);
        assert open'(0,x,t'')==s;
        RefBetaAbsIntro(t,t'',x);
        RefBetaPathAbsIntro'(t'',t',x,n-1);
        assert refBeta(RefLambda(t),RefLambda(t'')) && refBetaPath'(RefLambda(t''),RefLambda(t'),n-1);
    }
}

lemma RefBetaPathAbs(t:RefLambdaTerm, t':RefLambdaTerm, L:seq<Id>)
    requires allUnique(L)
    requires forall x:Id:: !(x in L) ==> refBetaPath(open'(0,x,t),open'(0,x,t'))
    ensures  refBetaPath(RefLambda(t),RefLambda(t'))
{
    var avoid := reunion(L,reunion(freeVarsSeq(t),freeVarsSeq(t')));
    var x:Id := addAnUniqueId(avoid)[0];
    NotInReunionSoNotInBoth(L,reunion(freeVarsSeq(t),freeVarsSeq(t')),x);
    NotInReunionSoNotInBoth(freeVarsSeq(t),freeVarsSeq(t'),x);
    var n:nat :| refBetaPath'(open'(0,x,t),open'(0,x,t'),n);
    RefBetaPathAbsIntro'(t,t',x,n);
}


lemma RefBetaPathTransitive(t1:RefLambdaTerm, t2:RefLambdaTerm, t3:RefLambdaTerm)
    requires refBetaPath(t1,t2) && refBetaPath(t2,t3)
    ensures  refBetaPath(t1,t3)
{
    var n1:nat:|refBetaPath'(t1,t2,n1);
    var n2:nat:|refBetaPath'(t2,t3,n2);
    RefBetaPathTransitive'(t1,t2,t3,n1,n2);
}
lemma RefBetaPathExtension(t1:RefLambdaTerm,t2:RefLambdaTerm,t2':RefLambdaTerm,n:nat)
    requires refBetaPath'(t1,t2,n)
    requires refBeta(t2,t2')
    decreases n
    ensures refBetaPath'(t1,t2',n+1)
{
    if n==0
    {
        assert t1==t2;
        assert refBetaPath'(t2',t2',0);
        assert refBeta(t1,t2') && refBetaPath'(t2',t2',0);
    }
    else
    {
        var t':RefLambdaTerm :| refBeta(t1,t') && refBetaPath'(t',t2,n-1);
        RefBetaPathExtension(t',t2,t2',n-1);
        assert refBetaPath'(t',t2',n);
        assert refBeta(t1,t') && refBetaPath'(t',t2',n);
    }
}
lemma RefBetaPathTransitive'(t1:RefLambdaTerm, t2:RefLambdaTerm, t3:RefLambdaTerm,n1:nat,n2:nat)
    requires refBetaPath'(t1,t2,n1) && refBetaPath'(t2,t3,n2)
    decreases n2
    ensures  refBetaPath'(t1,t3,n1+n2)
{
    if n2==0
    {
        assert t2==t3;
        assert refBetaPath'(t1,t3,n1+0);
    }
    else 
    {
        var t2':RefLambdaTerm:|refBeta(t2,t2') &&  refBetaPath'(t2',t3,n2-1);
        RefBetaPathExtension(t1,t2,t2',n1);
        assert refBetaPath'(t1,t2',n1+1);
        RefBetaPathTransitive'(t1,t2',t3,n1+1,n2-1);
    }
}

lemma RefBetaStep(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires refBeta(t1,t2)
    ensures  refBetaPath(t1,t2)
{
    var n:=1;
    assert refBetaPath'(t1,t2,1);
}

lemma RefBetaPathApp1(t1:RefLambdaTerm, t1':RefLambdaTerm, t2:RefLambdaTerm)
    requires refBetaPath(t1,t1') && locallyClosed(t2)
    ensures  refBetaPath(App(t1,t2),App(t1',t2))
{
    var n:nat:| refBetaPath'(t1,t1',n);
    RefBetaPathApp1'(t1,t1',t2,n);
}

lemma RefBetaPathApp1'(t1:RefLambdaTerm, t1':RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    requires refBetaPath'(t1,t1',n) && locallyClosed(t2)
    decreases n
    ensures  refBetaPath'(App(t1,t2),App(t1',t2),n)
{
    if n == 0 {
        assert t1 == t1';
        assert App(t1,t2) == App(t1',t2);
        assert refBetaPath'(App(t1,t2),App(t1',t2), 0);
    } else {
        var t':RefLambdaTerm :| refBeta(t1, t') && refBetaPath'(t', t1', n-1);
        
       
        RefBetaPathApp1'(t', t1', t2, n-1);
        assert refBetaPath'(App(t',t2), App(t1',t2), n-1);
        

        assert betaRuleApp1(App(t1,t2), App(t',t2)) by {
            assert locallyClosed(t2);
            assert refBeta(t1, t');
        }
        RefBetaIntro(App(t1,t2), App(t',t2));
        assert refBeta(App(t1,t2), App(t',t2));
        
      
        assert refBetaPath'(App(t1,t2), App(t1',t2), n);
    }
}

lemma RefBetaPathApp2(t1:RefLambdaTerm, t2:RefLambdaTerm, t2':RefLambdaTerm)
    requires locallyClosed(t1) && refBetaPath(t2,t2')
    ensures  refBetaPath(App(t1,t2),App(t1,t2'))
{
     var n:nat:| refBetaPath'(t2,t2',n);
    RefBetaPathApp2'(t1,t2',t2,n);
}
lemma RefBetaPathApp2'(t1:RefLambdaTerm, t2':RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    requires refBetaPath'(t2,t2',n) && locallyClosed(t1)
    decreases n
    ensures  refBetaPath'(App(t1,t2),App(t1,t2'),n)
{
    if n == 0 {
        assert t2 == t2';
        assert App(t1,t2) == App(t1,t2');
        assert refBetaPath'(App(t1,t2),App(t1,t2'), 0);
    } else {
        var t':RefLambdaTerm :| refBeta(t2, t') && refBetaPath'(t', t2', n-1);
        
       
        RefBetaPathApp2'(t1, t2', t', n-1);
        assert refBetaPath'(App(t1,t'), App(t1,t2'), n-1);
        

        assert betaRuleApp2(App(t1,t2), App(t1,t')) by {
            assert locallyClosed(t1);
            assert refBeta(t2, t');
        }
        RefBetaIntro(App(t1,t2), App(t1,t'));
        assert refBeta(App(t1,t2), App(t1,t'));
        
      
        assert refBetaPath'(App(t1,t2), App(t1,t2'), n);
    }
}

lemma RefBetaPathRegular(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires refBetaPath(t1,t2) && t1!=t2
    ensures  locallyClosed(t1) && locallyClosed(t2)
{
    var n:nat:|refBetaPath'(t1,t2,n);
    RefBetaPathRegular'(t1,t2,n);
}

lemma RefBetaPathRegular'(t1:RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    requires refBetaPath'(t1,t2,n)
    requires t1!=t2
    decreases n
    ensures  locallyClosed(t1) && locallyClosed(t2)
{

    assert n > 0; 


    var t':RefLambdaTerm :| refBeta(t1, t') && refBetaPath'(t', t2, n-1);
    
   
    RefBetaRegular(t1, t');
    assert locallyClosed(t1) && locallyClosed(t');

    if t' == t2 {
      
        assert locallyClosed(t2);
    } else {

        RefBetaPathRegular'(t', t2, n-1);
    }
}

lemma RefBetaImpliesParallel(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires refBeta(t1,t2)
    ensures  refParallelReduction(t1,t2)
    decreases refLHeight(t1)
{
    if betaRuleApp1(t1,t2)
    {
        var t1a:RefLambdaTerm,t1b:RefLambdaTerm:|t1==App(t1a,t1b);
        var t2a:RefLambdaTerm,t2b:RefLambdaTerm:|t2==App(t2a,t2b);

        assert t2b==t1b;
        refParaReductionReflexive(t1b);
        RefBetaImpliesParallel(t1a,t2a);
    }
    else 
    {
        if betaRuleApp2(t1,t2)
        {
            var t1a:RefLambdaTerm,t1b:RefLambdaTerm:|t1==App(t1a,t1b);
            var t2a:RefLambdaTerm,t2b:RefLambdaTerm:|t2==App(t2a,t2b);

            assert t2a==t1a;
            refParaReductionReflexive(t1a);
            RefBetaImpliesParallel(t1b,t2b);
            

        }
        else 
        {
            if betaRuleAbs(t1,t2)
            {
                var t1':RefLambdaTerm,t2':RefLambdaTerm:| t1==RefLambda(t1') && t2==RefLambda(t2');
                var L:seq<Id>:|allUnique(L) &&
                    forall x:Id:: !(x in L) ==> refBeta(open'(0,x,t1'),open'(0,x,t2'));
                Rule2Intro(t1',t2',L);
            }
            else 
            {
                assert betaRuleRedex(t1,t2);
                var t1a':RefLambdaTerm,t1b:RefLambdaTerm:|t1==App(RefLambda(t1a'),t1b);

                assert t2==opening(t1a',0,t1b);
                refParaReductionReflexive(t1b);
                forall x:Id|!(x in [])
                    ensures refParallelReduction(open'(0,x,t1a'),open'(0,x,t1a'))
                {
                    IfWeForgetThatIsOpenedItThenIsClosed'(t1a',x,1);
                    refParaReductionReflexive(open'(0,x,t1a'));
                }
                
                Rule3Intro(t1a',t1b,t1a',t1b,[]);
            }
        }
    }
}
lemma RefBetaPathImpliesParallelPath'(t1:RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    requires refBetaPath'(t1,t2,n)
    decreases n 
    ensures  isThereAParallelPath'(t1,t2,n)
{
    if n==0
    {
        assert t1==t2;
    }
    else 
    {
        var t':RefLambdaTerm:|refBeta(t1,t') && refBetaPath'(t',t2,n-1);

        RefBetaImpliesParallel(t1,t');
        RefBetaPathImpliesParallelPath'(t',t2,n-1);
        assert refParallelReduction(t1,t') && isThereAParallelPath'(t',t2,n-1);
        
    }
}

lemma ParallelImpliesRefBetaPath(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t1) && refParallelReduction(t1,t2)
    decreases refLHeight(t1)
    ensures  refBetaPath(t1,t2)
{
    if (refRule1(t1,t2))
    {
        assert t1==t2;
        assert refBetaPath'(t1,t2,0);
    }
    else 
    {
        if refRule2(t1,t2)
        {
            var t1':RefLambdaTerm,t2':RefLambdaTerm:|t1==RefLambda(t1') && t2==RefLambda(t2');
            var L:seq<Id>:|allUnique(L) && forall x:Id::!(x in L)==> refParallelReduction(open'(0,x,t1'),open'(0,x,t2'));
            assert  forall x:Id::!(x in L)==>refParallelReduction(open'(0,x,t1'),open'(0,x,t2'));
            forall x:Id | !(x in L)
                ensures refBetaPath(open'(0,x,t1'), open'(0,x,t2'))
                {
                   
                    IfWeForgetThatIsOpenedItThenIsClosed(t1, x); 
                    ParallelImpliesRefBetaPath(open'(0,x,t1'), open'(0,x,t2'));
                }
            RefBetaPathAbs(t1', t2', L);
        }
        else
        {
            if refRule3(t1,t2)
            {
                var t1a':RefLambdaTerm, t1b:RefLambdaTerm :| t1 == App(RefLambda(t1a'), t1b);
                var t2a':RefLambdaTerm, t2b:RefLambdaTerm, L:seq<Id> :| 
                    t2 == opening(t2a', 0, t2b) && 
                    refParallelReduction(t1b, t2b) && 
                    allUnique(L) && 
                    (forall x:Id :: !(x in L) ==> refParallelReduction(open'(0,x,t1a'), open'(0,x,t2a')));

                ParallelImpliesRefBetaPath(t1b, t2b);

                forall x:Id | !(x in L)
                    ensures refBetaPath(open'(0,x,t1a'), open'(0,x,t2a'))
                {
                    IfWeForgetThatIsOpenedItThenIsClosed(RefLambda(t1a'), x);
                    assert refLHeight(t1a')<refLHeight(t1);
                    ParallelImpliesRefBetaPath(open'(0,x,t1a'), open'(0,x,t2a'));
                }
                RefBetaPathAbs(t1a', t2a', L); 

                Rule2Intro(t1a', t2a', L); 
                ParReductionPreservesLocallyClosed(RefLambda(t1a'), RefLambda(t2a'));

                RefBetaPathApp1(RefLambda(t1a'), RefLambda(t2a'), t1b);
                RefBetaPathApp2(RefLambda(t2a'), t1b, t2b);
                RefBetaPathTransitive(t1, App(RefLambda(t2a'), t1b), App(RefLambda(t2a'), t2b));

                assert betaRuleRedex(App(RefLambda(t2a'), t2b), t2) by {
                    assert locallyClosed'(t2a', 1);
                    ParReductionPreservesLocallyClosed(t1b, t2b);
                }
                RefBetaIntro(App(RefLambda(t2a'), t2b), t2);
                RefBetaStep(App(RefLambda(t2a'), t2b), t2);

                RefBetaPathTransitive(t1, App(RefLambda(t2a'), t2b), t2);
            }
            else 
            {
                assert refRule4(t1,t2);
                var t1a:RefLambdaTerm, t1b:RefLambdaTerm :| t1 == App(t1a, t1b);
                var t2a:RefLambdaTerm, t2b:RefLambdaTerm :| t2 == App(t2a, t2b);

                ParallelImpliesRefBetaPath(t1a, t2a);
                ParallelImpliesRefBetaPath(t1b, t2b);

                ParReductionPreservesLocallyClosed(t1a, t2a);

                RefBetaPathApp1(t1a, t2a, t1b);
                RefBetaPathApp2(t2a, t1b, t2b);

                RefBetaPathTransitive(t1, App(t2a, t1b), t2);
            }
        }
    }
}


lemma StripLemma'(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    requires locallyClosed(t)
    requires refParallelReduction(t, t1)
    requires isThereAParallelPath'(t, t2, n)
    decreases n
    ensures  exists t3:RefLambdaTerm :: isThereAParallelPath(t1, t3) && isThereAParallelPath(t2, t3)
{
    if (n==0)
    {
        assert t==t2;
        ParReductionPreservesLocallyClosed(t,t1);
        refParaReductionReflexive(t1);
        assert isThereAParallelPath'(t1,t1,0) && isThereAParallelPath'(t2,t1,1);
        var t3:=t1;
        assert isThereAParallelPath(t1,t1) && isThereAParallelPath(t2,t1);
    }
    else 
    {
        var t':RefLambdaTerm:|refParallelReduction(t,t') && isThereAParallelPath'(t',t2,n-1);
        ParReductionPreservesLocallyClosed(t,t');
        ParDiamond(t,t1,t');
        var t3:RefLambdaTerm:|refParallelReduction(t1,t3) && refParallelReduction(t',t3);
        StripLemma'(t',t3,t2,n-1);
        var t3':RefLambdaTerm:|isThereAParallelPath(t3,t3') && isThereAParallelPath(t2,t3');
        assert isThereAParallelPath'(t1,t3,1);
        ParallelPathTransitive(t1,t3,t3');
    }
}

lemma StripLemma(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t)
    requires refParallelReduction(t, t1)
    requires isThereAParallelPath(t, t2)
    ensures  exists t3:RefLambdaTerm :: isThereAParallelPath(t1, t3) && isThereAParallelPath(t2, t3)
{
    var n:nat:|isThereAParallelPath'(t,t2,n);
    StripLemma'(t,t1,t2,n);
}


lemma ParallelPathDiamond'(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm, n1:nat)
    requires locallyClosed(t)
    requires isThereAParallelPath'(t, t1, n1)
    requires isThereAParallelPath(t, t2)
    decreases n1
    ensures  exists t3:RefLambdaTerm :: isThereAParallelPath(t1, t3) && isThereAParallelPath(t2, t3)
{
    if n1==0
    {
        assert t == t1;
        assert isThereAParallelPath'(t2, t2, 0);
        assert isThereAParallelPath(t1, t2) && isThereAParallelPath(t2, t2);
    }
    else
    {
        var t':RefLambdaTerm :| refParallelReduction(t, t') && isThereAParallelPath'(t', t1, n1-1);
        
        StripLemma(t, t', t2);
        var t2':RefLambdaTerm :| isThereAParallelPath(t', t2') && isThereAParallelPath(t2, t2');

        ParReductionPreservesLocallyClosed(t, t');
        
        ParallelPathDiamond'(t', t1, t2', n1-1);
        var t3:RefLambdaTerm :| isThereAParallelPath(t1, t3) && isThereAParallelPath(t2', t3);

        ParallelPathTransitive(t2, t2', t3);
    }
}

lemma ParallelPathDiamond(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t)
    requires isThereAParallelPath(t, t1)
    requires isThereAParallelPath(t, t2)
    ensures  exists t3:RefLambdaTerm :: isThereAParallelPath(t1, t3) && isThereAParallelPath(t2, t3)
{
     var n:nat:|isThereAParallelPath'(t,t1,n);
     ParallelPathDiamond'(t,t1,t2,n);
}

lemma ParallelPathImpliesRefBetaPath'(t1:RefLambdaTerm, t2:RefLambdaTerm, n:nat)
    requires locallyClosed(t1)
    requires isThereAParallelPath'(t1, t2, n)
    decreases n
    ensures  refBetaPath(t1, t2)
{
    if n == 0 {
        assert t1 == t2;
        assert refBetaPath'(t1, t2, 0);
    } else {
        var t':RefLambdaTerm :| refParallelReduction(t1, t') && isThereAParallelPath'(t', t2, n-1);
        
        ParallelImpliesRefBetaPath(t1, t');
        ParReductionPreservesLocallyClosed(t1, t');
        
        ParallelPathImpliesRefBetaPath'(t', t2, n-1);
        RefBetaPathTransitive(t1, t', t2);
    }
}

lemma ParallelPathImpliesRefBetaPath(t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t1)
    requires isThereAParallelPath(t1, t2)
    ensures  refBetaPath(t1, t2)
{
    var n:nat :| isThereAParallelPath'(t1, t2, n);
    ParallelPathImpliesRefBetaPath'(t1, t2, n);
}

lemma ChurchRosserTheorem(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t)
    requires refBetaPath(t, t1)
    requires refBetaPath(t, t2)
    ensures  exists t3:RefLambdaTerm :: refBetaPath(t1, t3) && refBetaPath(t2, t3)
{
    if t == t1 {
        assert refBetaPath'(t1, t1, 0);
    }
    
    var n1:nat :| refBetaPath'(t, t1, n1);
    RefBetaPathImpliesParallelPath'(t, t1, n1);

    var n2:nat :| refBetaPath'(t, t2, n2);
    RefBetaPathImpliesParallelPath'(t, t2, n2);

    ParallelPathDiamond(t, t1, t2);
    var t3:RefLambdaTerm :| isThereAParallelPath(t1, t3) && isThereAParallelPath(t2, t3);

    if t != t1 {
        RefBetaPathRegular(t, t1);
    }
    if t != t2 {
        RefBetaPathRegular(t, t2);
    }
    assert locallyClosed(t1) && locallyClosed(t2);

    ParallelPathImpliesRefBetaPath(t1, t3);
    ParallelPathImpliesRefBetaPath(t2, t3);
}