(function(root){
'use strict';
const rows=[
 ['4.1.1',6,'consistency','첫걸음 · 가지 하나의 모순',['~~B','C','~A','~(B->C)']],
 ['4.1.2',9,'consistency','첫걸음 · 열린 가지',['D&~A','~(BvA)','~~D','~(~A->B)']],
 ['4.2.1',10,'consistency','조건문과 선언의 가지치기',['A->(BvC)','A&~C']],
 ['4.2.1',11,'consistency','조건문과 쌍조건문',['A->(B&~C)','C<->~A']],
 ['5.1.1',12,'consistency','가지치기 없는 규칙부터',['~A->(B->~C)','~(B->D)','~(AvC)']],
 ['5.2.1',13,'consistency','닫히는 가지를 먼저 찾기',['A->B','B->A','~A']],
 ['5.3.1',14,'consistency','세 문장의 일관성',['A->(B&~C)','~(CvA)','C<->~A']],
 ['5.3.2',15,'consistency','복합 쌍조건문의 분해',['(C&~D)<->A','(A&C)->~(DvA)']],
 ['6.1.1',17,'validity','결론 B의 타당성',['(~Bv~H)->M','K&~M'],'B'],
 ['6.1.2',17,'validity','결론 J & H의 반례',['~W&~L','(J->~W)<->~L','H'],'J&H'],
 ['6.1.3',18,'validity','결론 ~(J & H)의 반례',['~W&~L','(J->~W)<->~L','H'],'~(J&H)'],
 ['6.1.4',19,'validity','조건문과 선언 논증',['(G->B)&(~G->N)','Bv~N'],'Nv~B'],
 ['6.1.5',19,'validity','복합 조건문 논증',['[(F&~B)vQ]->[A&(SvT)]','F&~(S&A)','SvA'],'B->(A->S)'],
 ['7.4.1 (1)',21,'tautology','논리적 참 판정 ①','[(FvG)->(P&Q)]->(~Q->~F)'],
 ['7.4.1 (2)',21,'tautology','논리적 참 판정 ②','[Lv(M&N)]->[(LvM)&N]'],
 ['7.4.2 (1)',21,'contradiction','논리적 거짓 판정 ①','[(H&F)->C]&~[H->(F->C)]'],
 ['7.4.2 (2)',21,'contradiction','논리적 거짓 판정 ②','~{[B&(Mv~P)]->[P->(~Mv~B)]}'],
 ['7.4.3 (1)',21,'equivalence','두 조건문의 동치 ①',['(D&N)->J','D->(N->J)']],
 ['7.4.3 (2)',21,'equivalence','두 조건문의 동치 ②',['(I->Q)->D','I->(Q->D)']]
];
const problems=rows.map(([section,page,kind,title,data,goal],i)=>({id:'tree6-'+(i+1),section,page,kind,title,...(kind==='validity'?{premises:data,goal}:['tautology','contradiction'].includes(kind)?{formula:data}:{formulas:data}),note:i===3?'원문에서 p.10과 p.11의 번호가 모두 4.2.1입니다. 쪽수로 구별합니다.':i===7?'원문 p.15의 ~(DvA에 빠진 닫는 괄호를 보완했습니다.':i===10?'원문 p.18에 같은 6.1.3 문제가 두 번 나와 한 번만 수록했습니다.':''}));
if(typeof module!=='undefined')module.exports=problems;else root.TREE_PROBLEMS=problems;
})(globalThis);
