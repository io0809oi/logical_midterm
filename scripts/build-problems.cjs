process.chdir(require('node:path').resolve(__dirname,'..'));
const fs=require('node:fs');const L=require('../dist/logic.js');const {parse,format,op,eq,neg,contra}=L;
const key=a=>JSON.stringify(a),B=(k,a,b)=>[k,a,b];
class Proof{
 constructor(p){this.p=p;this.s=L.initial(p.premises);this.out=[];this.ops=0}
 emit(a,r,refs=[]){let f=typeof a==='string'&&a!=='⊥'?a:format(a),rs=Array.isArray(refs)?refs.join(','):refs;try{this.s=L.add(this.s,f,r,rs,this.p.allowed)}catch(e){throw Error(this.p.id+' at '+(this.s.lines.length+1)+' '+f+' '+r+' '+rs+': '+e.message)}this.out.push([f,r,rs]);return this.s.lines.length}
 ctx(){return new Map(this.s.lines.map((l,i)=>[l,i+1]).filter(([l])=>L.prefix(l.path,this.s.stack)).map(([l,n])=>[key(l.a),n]))}
 ast(k){return JSON.parse(k)}
 ensure(ctx,a,r,refs){let k=key(a);if(ctx.has(k))return ctx.get(k);let n=this.emit(a,r,refs);ctx.set(k,n);return n}
 assume(a){return this.emit(a,'가정')}
 discharge(a,r,start){return this.emit(a,r,start+'-'+this.s.lines.length)}
 repeat(n){let l=this.s.lines[n-1];if(n!==this.s.lines.length||!eq(l.path,this.s.stack))return this.emit(l.a,'R',[n]);return n}
 explode(a,bottom){let st=this.assume(neg(a));this.emit('⊥','R',[bottom]);let nn=this.discharge(neg(neg(a)),'~I',st);return this.emit(a,'~E',[nn])}
 saturate(ctx){let changed=true;while(changed){changed=false;for(const [k,n] of [...ctx]){let a=this.ast(k),items=[];if(op(a,'∧'))items=[[a[1],'&E',[n]],[a[2],'&E',[n]]];if(op(a,'¬')&&op(a[1],'¬'))items=[[a[1][1],'~E',[n]]];if(op(a,'↔'))items=[[B('→',a[1],a[2]),'<->E',[n]],[B('→',a[2],a[1]),'<->E',[n]]];if(op(a,'→')&&ctx.has(key(a[1])))items.push([a[2],'->E',[n,ctx.get(key(a[1]))]]);if(op(a,'∨'))for(const [q,m] of ctx){let b=this.ast(q);if(contra(a[1],b))items.push([a[2],'vE',[n,m]]);if(contra(a[2],b))items.push([a[1],'vE',[n,m]])}for(const [b,r,refs] of items)if(!ctx.has(key(b))){this.ensure(ctx,b,r,refs);changed=true}}}return ctx}
 contradiction(ctx){if(ctx.has(key('⊥')))return this.repeat(ctx.get(key('⊥')));for(const [k,n] of ctx){let a=this.ast(k);if(op(a,'¬')&&ctx.has(key(a[1])))return this.emit('⊥','⊥I',[n,ctx.get(key(a[1]))])}return null}
 refute(ctx,done=new Set()){
 if(++this.ops>2000)throw Error('proof search too long '+this.p.id);let c=this.contradiction(ctx);if(c)return c;this.saturate(ctx);c=this.contradiction(ctx);if(c)return c;
 const entries=[...ctx].filter(([k])=>!done.has(k));
 // Non-branching expansions, each compiled to basic classroom rules.
 for(const [k,n] of entries){let a=this.ast(k);if(!op(a,'¬')||!Array.isArray(a[1]))continue;let x=a[1],nd=new Set(done);nd.add(k);
 if(op(x,'∨')){for(let i=1;i<=2;i++){let st=this.assume(x[i]),d=this.emit(x,'vI',[st]);this.emit('⊥','⊥I',[n,d]);let nn=this.discharge(neg(x[i]),'~I',st);ctx.set(key(neg(x[i])),nn)}return this.refute(ctx,nd)}
 if(op(x,'→')){let st=this.assume(neg(x[1])),ast=this.assume(x[1]),bot=this.emit('⊥','⊥I',[st,ast]);this.explode(x[2],bot);let imp=this.discharge(x,'->I',ast);this.emit('⊥','⊥I',[n,imp]);let nn=this.discharge(neg(neg(x[1])),'~I',st);let an=this.emit(x[1],'~E',[nn]);ctx.set(key(x[1]),an);let bst=this.assume(x[2]),pst=this.assume(x[1]);this.emit(x[2],'R',[bst]);imp=this.discharge(x,'->I',pst);this.emit('⊥','⊥I',[n,imp]);let nb=this.discharge(neg(x[2]),'~I',bst);ctx.set(key(neg(x[2])),nb);return this.refute(ctx,nd)}
 if(op(x,'↔')){let both=B('∧',B('→',x[1],x[2]),B('→',x[2],x[1])),st=this.assume(both),l=this.emit(both[1],'&E',[st]),r=this.emit(both[2],'&E',[st]),iff=this.emit(x,'<->I',[l,r]);this.emit('⊥','⊥I',[n,iff]);let nn=this.discharge(neg(both),'~I',st);ctx.set(key(neg(both)),nn);return this.refute(ctx,nd)}
 }
 // Branching tableau steps with assumptions discharged by ~I.
 for(const [k,n] of entries){let a=this.ast(k),nd=new Set(done);nd.add(k);
 if(op(a,'∨')){let st=this.assume(a[1]),branch=new Map(ctx);branch.set(key(a[1]),st);this.refute(branch,nd);let na=this.discharge(neg(a[1]),'~I',st);ctx.set(key(neg(a[1])),na);let bn=this.emit(a[2],'vE',[n,na]);ctx.set(key(a[2]),bn);return this.refute(ctx,nd)}
 if(op(a,'→')){let st=this.assume(a[1]),bn=this.emit(a[2],'->E',[n,st]),branch=new Map(ctx);branch.set(key(a[1]),st);branch.set(key(a[2]),bn);this.refute(branch,nd);let na=this.discharge(neg(a[1]),'~I',st);ctx.set(key(neg(a[1])),na);return this.refute(ctx,nd)}
 if(op(a,'¬')&&op(a[1],'∧')){let x=a[1],st=this.assume(x[1]),bst=this.assume(x[2]),ab=this.emit(x,'&I',[st,bst]);this.emit('⊥','⊥I',[n,ab]);let nb=this.discharge(neg(x[2]),'~I',bst),branch=new Map(ctx);branch.set(key(x[1]),st);branch.set(key(neg(x[2])),nb);this.refute(branch,nd);let na=this.discharge(neg(x[1]),'~I',st);ctx.set(key(neg(x[1])),na);return this.refute(ctx,nd)}
 }
 throw Error('Open branch (invalid argument?) '+this.p.id+' '+[...ctx.keys()].join(' '));
 }
 prove(g){let ctx=this.saturate(this.ctx());if(ctx.has(key(g)))return this.repeat(ctx.get(key(g)));if(g==='⊥')return this.refute(ctx);if(op(g,'∧')){let a=this.prove(g[1]),b=this.prove(g[2]);return this.emit(g,'&I',[a,b])}if(op(g,'→')){let st=this.assume(g[1]);this.prove(g[2]);return this.discharge(g,'->I',st)}if(op(g,'↔')){let a=this.prove(B('→',g[1],g[2])),b=this.prove(B('→',g[2],g[1]));return this.emit(g,'<->I',[a,b])}if(op(g,'¬')){this.assume(g[1]);let st=this.s.lines.length;this.refute(this.ctx());return this.discharge(g,'~I',st)}let st=this.assume(neg(g));this.refute(this.ctx());let nn=this.discharge(neg(neg(g)),'~I',st);return this.emit(g,'~E',[nn])}
}
const problems=[];
function add(id,title,level,premises,goal,source,page,section,hint,extra={}){problems.push({id,title,level,premises,goal,source,page,section,hint,allowed:L.basicRules,...extra})}
const h4=(id,title,level,ps,g,page,section,hint,extra)=>add('h4-'+id,title,level,ps,g,'핸드아웃 4',page,section,hint,extra);
const h5=(id,title,level,ps,g,page,section,hint,extra)=>add('h5-'+id,title,level,ps,g,'핸드아웃 5',page,section,hint,extra);
const own=(id,title,level,ps,g,hint,extra)=>add('own-'+id,title,level,ps,g,'창작',null,'추가 연습',hint,extra);
const h41=(id,title,level,ps,g,section,hint,extra={})=>add('h41-'+id,title,level,ps,g,'추가 연습 4.1',1,section,hint,{sourceFile:'handout-4-1.pdf',...extra});
// Uploaded 4.1 worksheet: retain the original section and question numbers.
h41('t1','추가 연습 1-1 · 조건문의 연쇄','기초',[],'(Q->R)->((P->Q)->(P->R))','1. 필연적 참 · 1번','Q → R, P → Q, P를 차례로 가정한 뒤 Q와 R을 도출하세요.',{solution:[['Q->R','가정',''],['P->Q','가정',''],['P','가정',''],['Q','->E','2,3'],['R','->E','1,4'],['P->R','->I','3-5'],['(P->Q)->(P->R)','->I','2-6'],['(Q->R)->((P->Q)->(P->R))','->I','1-7']]});
h41('t2','추가 연습 1-2 · 두 경우의 같은 결론','중급',[],'(P->R)->((Q->R)->((P v Q)->R))','1. 필연적 참 · 2번','세 전건을 가정한 뒤 ~R을 가정하세요. P가 모순임을 보이면 ~P와 P v Q에서 Q를 얻습니다.',{note:'원문 1-2 끝의 여분 닫는 괄호 한 개를 바로잡았습니다. 논리적 내용은 동일합니다.',solution:[['P->R','가정',''],['Q->R','가정',''],['P v Q','가정',''],['~R','가정',''],['P','가정',''],['R','->E','1,5'],['⊥','⊥I','4,6'],['~P','~I','5-7'],['Q','vE','3,8'],['R','->E','2,9'],['⊥','⊥I','4,10'],['~~R','~I','4-11'],['R','~E','12'],['(P v Q)->R','->I','3-13'],['(Q->R)->((P v Q)->R)','->I','2-14'],['(P->R)->((Q->R)->((P v Q)->R))','->I','1-15']]});
h41('t3','추가 연습 1-3 · 모순으로 가정 부정','기초',[],'(P->(Q&~Q))->~P','1. 필연적 참 · 3번','P를 가정하면 Q와 ~Q를 함께 얻습니다. ⊥I, ~I 순서로 적용하세요.',{solution:[['P->(Q&~Q)','가정',''],['P','가정',''],['Q&~Q','->E','1,2'],['Q','&E','3'],['~Q','&E','3'],['⊥','⊥I','4,5'],['~P','~I','2-6'],['(P->(Q&~Q))->~P','->I','1-7']]});
h41('t4','추가 연습 1-4 · 부정에서 원명제로','중급',[],'(~P->P)->P','1. 필연적 참 · 4번','~P → P를 가정한 뒤 ~P를 가정하세요. 모순에서 ~~P를 얻고 ~E를 적용합니다.',{solution:[['~P->P','가정',''],['~P','가정',''],['P','->E','1,2'],['⊥','⊥I','2,3'],['~~P','~I','2-4'],['P','~E','5'],['(~P->P)->P','->I','1-6']]});
h41('t5','추가 연습 1-5 · 선언 속 조건문','심화',[],'P v (P->Q)','1. 필연적 참 · 5번','결론의 부정을 가정하세요. P를 가정하면 선언 도입으로 모순이 생깁니다. ~P를 얻은 뒤 P → Q를 만들어 보세요.');
h41('v1','추가 연습 2-1 · 연언 후건의 부정','기초',['P->(Q&R)','~Q'],'~P','2. 타당성 · 1번','P를 가정해 Q & R을 얻고, Q를 꺼내 ~Q와 모순을 만드세요.',{solution:[['P','가정',''],['Q&R','->E','1,3'],['Q','&E','4'],['⊥','⊥I','2,5'],['~P','~I','3-6']]});
h41('v2','추가 연습 2-2 · 두 조건문의 선언','심화',['(P&Q)->R'],'(P->R) v (Q->R)','2. 타당성 · 2번','결론의 부정을 가정하고 각 조건문을 가정했을 때 모순이 됨을 이용하세요. P와 Q가 함께 있으면 R을 얻을 수 있습니다.');
h41('v3','추가 연습 2-3 · 조건문과 선언','중급',['P->(~Q->R)'],'~Q->(~P v R)','2. 타당성 · 3번','~Q를 가정한 안에서 ~(~P v R)을 가정하세요. P로 R을 얻으면 모순이므로 ~P를 얻습니다.',{solution:[['~Q','가정',''],['~(~P v R)','가정',''],['P','가정',''],['~Q->R','->E','1,4'],['R','->E','2,5'],['~P v R','vI','6'],['⊥','⊥I','3,7'],['~P','~I','4-8'],['~P v R','vI','9'],['⊥','⊥I','3,10'],['~~(~P v R)','~I','3-11'],['~P v R','~E','12'],['~Q->(~P v R)','->I','2-13']]});
h41('v4','추가 연습 2-4 · 선언에서 남는 결론','중급',['P->(Q&R)','S->(P v T)','~R'],'S->T','2. 타당성 · 4번','P 가정에서 R과 ~R의 모순을 얻어 ~P를 도출하세요. S를 가정해 P v T를 얻고 vE를 적용합니다.',{solution:[['P','가정',''],['Q&R','->E','1,4'],['R','&E','5'],['⊥','⊥I','3,6'],['~P','~I','4-7'],['S','가정',''],['P v T','->E','2,9'],['T','vE','8,10'],['S->T','->I','9-11']]});
const restricted1=['->E','vE','vI','R'];const restricted2=[...restricted1,'->I','가정'];
h4('e1-1','연습 1 · 1번','기초',['A -> ~D','D v C','A'],'C v D',5,'연습 1 (1)','A로부터 ~D를 얻고, D v C에서 D를 제외하세요.',{allowed:restricted1,solution:[['~D','->E','1,3'],['C','vE','2,4'],['C v D','vI','5']]});
h4('e1-2','연습 1 · 2번','기초',['(M v ~T)->(A v J)','~A','B v M','~A -> ~B'],'J v D',6,'연습 1 (2)','~B를 얻어 M을 남긴 뒤, M v ~T를 만들어 첫 조건문을 사용하세요.',{allowed:restricted1,solution:[['~B','->E','2,4'],['M','vE','3,5'],['M v ~T','vI','6'],['A v J','->E','1,7'],['J','vE','8,2'],['J v D','vI','9']]});
h4('e2-1','연습 2 · 1번','기초',['A -> B'],'A -> (B v C)',6,'연습 2 (1)','A를 가정하고 B에서 B v C를 도입하세요.',{allowed:restricted2,solution:[['A','가정',''],['B','->E','1,2'],['B v C','vI','3'],['A -> (B v C)','->I','2-4']]});
h4('e2-2','연습 2 · 2번','기초',['A -> B','(B v P) -> C'],'A -> C',6,'연습 2 (2)','A 가정에서 B, B v P, C 순서로 이어가세요.',{allowed:restricted2,solution:[['A','가정',''],['B','->E','1,3'],['B v P','vI','4'],['C','->E','2,5'],['A -> C','->I','3-6']]});
h4('s1','전략 · 대우 증명','중급',['B -> ~A'],'A -> ~B',11,'전략 1·2 (1)','A를 가정한 안에서 B를 다시 가정하면 A와 ~A가 충돌합니다.');
h4('s2','전략 · 쌍조건문','심화',['A v B','~(A&B)'],'A <-> ~B',11,'전략 1·2 (2)','A에서 ~B를, ~B에서 A를 각각 도출하세요.');
h4('s3','전략 · 귀류법','중급',['A&B','~C -> ~B'],'C',11,'전략 3 (1)','~C를 가정하면 ~B와 B가 모순됩니다. ~~C를 얻은 뒤 ~E를 적용하세요.');
h4('s4','전략 · 중첩 귀류법','중급',['~F -> G','G -> ~E'],'E -> F',12,'전략 3 (2)','E를 가정한 뒤 ~F를 가정하여 ~E를 도출하세요.');
h4('s5','전략 · 복합 전제','심화',['(S&B) -> K','(G->P)&(G v P)','~B <-> (~P&G)'],'S -> K',12,'전략 4 (1)','S를 가정하세요. ~B를 가정하면 ~P와 G, 이어서 P를 얻어 모순입니다.');
h4('s6','전략 · 세 겹의 가정','심화',['H->(D->K)','(K&M)->P','I->~(M->P)'],'H->(D->~I)',12,'전략 4 (2)','H와 D로 K를 얻고, M을 가정해 P를 도출하여 M → P를 만드세요.');
h4('extra1','추가 연습 · 동치','기초',['~C -> B','B -> ~C'],'B <-> ~C',13,'추가 연습 (1)','양방향 조건문이 전제로 이미 주어졌습니다.');
h4('extra2','추가 연습 · 선언의 부정','중급',['~A','~B'],'~(A v B)',13,'추가 연습 (2)','A v B를 가정하고 ~A로 B를 얻으면 ~B와 모순입니다.');
h4('extra3','추가 연습 · 복합 선언','심화',['A v B','~B <-> (C v D)','(D&E) v [D&(F->G)]'],'A',13,'추가 연습 (3)','우선 D를 얻어 C v D를 만들면 ~B, 이어서 A를 얻습니다. 기본 규칙만 사용하세요.',{allowed:L.basicRules});
h4('true1','정리 · 조건문과 부정','심화',[],'(K->F)->[~F->~(K&P)]',17,'6.5.1 (1)','K → F, ~F, K & P를 차례로 가정해 F와 ~F를 만드세요.',{kind:'필연적 참'});
h4('true2','정리 · 복합 선언','심화',[],'(I&~J) v [(J&K) v ~(K&I)]',17,'6.5.1 (2)','전체 문장의 부정을 가정하고 각 선언지의 부정을 이끌어 모순을 찾으세요.',{kind:'필연적 참'});
h4('false1','필연적 거짓 · 1번','중급',['(H v ~B)&[(~B->H)&~H]'],'⊥',18,'6.5.2 (1)','주어진 문장을 전제로 삼아 ⊥를 도출하세요. ~H와 H v ~B에서 ~B를 얻습니다.',{kind:'필연적 거짓',note:'원문의 문장이 필연적으로 거짓임을 보이기 위해, 그 문장을 전제로 놓고 모순 ⊥를 도출하는 형식입니다.'});
h4('false2','필연적 거짓 · 2번','심화',['[(H&F)->C]&~[H->(F->C)]'],'⊥',18,'6.5.2 (2)','H와 F를 차례로 가정하면 C를 얻습니다. H → (F → C)를 도출해 그 부정과 충돌시키세요.',{kind:'필연적 거짓',note:'원문의 문장을 전제로 삼아 ⊥를 도출하면 그 문장의 필연적 거짓이 증명됩니다.'});
h4('incon1','비일관성 · 1번','중급',['F v T','(F v T)->(~F&~T)'],'⊥',18,'6.5.3 (1)','~F와 ~T를 얻은 뒤 F v T에 vE를 적용하세요.',{kind:'비일관성'});
h4('incon2','비일관성 · 2번','기초',['(G v K)->A','(A v H)->G','G&~A'],'⊥',18,'6.5.3 (2)','G에서 G v K를 만들어 A를 얻으면 ~A와 모순입니다.',{kind:'비일관성'});
const derivations=[
['dn','DN의 증명','P->~~P',1,'1.1','~P를 가정하여 P와 모순을 만든 뒤 ~I를 사용하세요.'],
['mt','MT의 증명','[(P->Q)&~Q]->~P',1,'1.2','연언 전제를 가정하고 두 구성 문장을 꺼낸 뒤, P 가정에서 모순을 만드세요.'],
['ca','CA의 증명','[(P->Q)&(Q->R)]->(P->R)',2,'1.3','P를 가정하면 Q, R 순서로 도출됩니다.'],
['cp','CP의 증명','(P->Q)->(~Q->~P)',2,'1.4','조건문, ~Q, P를 차례로 가정하여 Q와 ~Q를 얻으세요.'],
['w','W의 증명','Q->(P->Q)',2,'1.5','Q를 가정한 뒤 P를 가정하고, 바깥의 Q를 반복하세요.'],
['ac','AC의 증명','[(P v Q)&(P->R)&(Q->R)]->R',3,'1.6','~R을 가정하면 P도 Q도 유지할 수 없습니다. ~P와 P v Q로 Q를 얻으세요.'],
['cr','CR의 증명','(P v Q)<->(Q v P)',3,'1.7','각 방향에서 결론의 부정을 가정해 양쪽 선언지와 모순을 만드세요.'],
['ar','AR의 증명','(P v (Q v R))<->((P v Q) v R)',3,'1.8','양방향을 나누어 증명하고, 각 선언지의 경우를 기본 규칙으로 처리하세요.'],
['dr1','DR의 증명 · 연언 분배','(P&(Q v R))<->((P&Q) v (P&R))',4,'1.9 (1)','양방향 조건문을 도출하세요. 이 문제에서는 DR 자체를 사용할 수 없습니다.'],
['dr2','DR의 증명 · 선언 분배','(P v (Q&R))<->((P v Q)&(P v R))',4,'1.9 (2)','한 방향은 P v Q와 P v R을 각각 얻고, 반대 방향은 귀류법을 고려하세요.'],
['dm1','DM의 증명 · 선언 부정','~(P v Q)<->(~P&~Q)',4,'1.10 (1)','선언의 부정에서 각각의 부정을 얻고, 반대로는 P v Q를 가정해 모순을 만드세요.'],
['dm2','DM의 증명 · 연언 부정','~(P&Q)<->(~P v ~Q)',4,'1.10 (2)','~P v ~Q의 부정을 가정하면 P와 Q를 얻을 수 있습니다.'],
['c1','C의 증명 · 조건문','(P->Q)<->(~P v Q)',5,'1.11 (1)','역방향에서는 P를 가정하고 ~P v Q에 vE를 사용하세요.'],
['c2','C의 증명 · 조건문 부정','~(P->Q)<->(P&~Q)',5,'1.11 (2)','조건문의 부정은 전건이 참이고 후건이 거짓인 경우입니다. 두 방향을 기본 규칙으로 증명하세요.']];
for(const [id,t,g,pg,sec,hint] of derivations)h5('proof-'+id,t,['dn','w'].includes(id)?'중급':'심화',[],g,pg,sec+' · 파생 규칙 증명',hint,{kind:'규칙 증명',note:'파생 규칙 자체를 증명하는 문제이므로, 10가지 기본 규칙과 ⊥I·R·가정만 사용할 수 있습니다.'});
const derived={allowed:L.allRules};
h5('e1','파생 규칙 연습 · 1번','중급',['A v B','~B <-> (C v D)','(D&E) v [D&(F->G)]'],'A',6,'2장 1.1 (1)','DR을 역방향으로 적용하면 D & (E v (F → G))를 얻습니다.',derived);
h5('e2','파생 규칙 연습 · 2번','중급',['~A->B','B->~C'],'C->A',6,'2장 1.1 (2)','CA로 ~A → ~C를 만들고 C 가정에서 MT와 ~E를 사용하세요.',derived);
h5('e3','파생 규칙 연습 · 3번','심화',['~A->[(B->D)->(A v ~C)]','(B->C)->~A','B->D','D->C'],'~D',6,'2장 1.1 (3)','CA로 B → C를 얻어 ~A를 도출하세요. A v ~C에서 ~C를 얻은 뒤 MT를 쓰세요.',derived);
h5('e4','파생 규칙 연습 · 4번','중급',['~A->(C&B)','~D->(B&E)','~A v ~D'],'B',6,'2장 1.1 (4)','~A → B와 ~D → B를 각각 만든 뒤 AC를 적용하세요.',derived);
h5('t1','파생 규칙 정리 · 1번','중급',[],'(A->B)->[~B->~(A&C)]',7,'2.2 (1)','A → B와 ~B로 MT를 적용해 ~A를 얻으세요.',{...derived,kind:'필연적 참'});
h5('t2','파생 규칙 정리 · 2번','심화',[],'(A&~B) v [(B&C) v ~(C&A)]',7,'2.2 (2)','전체 부정에 DM을 적용하고, C & A를 얻어 두 다른 선언지의 부정과 충돌시키세요.',{...derived,kind:'필연적 참'});
h5('t3','파생 규칙 정리 · 3번','중급',[],'[(A->B)&(A->~B)]->~A',7,'2.2 (3)','A를 가정하면 B와 ~B를 모두 얻습니다.',{...derived,kind:'필연적 참'});
h5('t4','파생 규칙 정리 · 4번','중급',[],'[(A->C)&(B->C)]->[(A v B)->C]',7,'2.2 (4)','두 조건문과 A v B를 모으면 AC를 적용할 수 있습니다.',{...derived,kind:'필연적 참'});
h5('lang1','기호화 · 사형 제도 논증','심화',['(~C&J)->R','C->D','~(C&D)','~R'],'~J',8,'3.2 (1)','C를 가정해 D를 얻으면 ~(C & D)와 모순입니다. ~C를 얻은 뒤 J를 가정하세요.',{...derived,kind:'기호화 연습',note:'원문 논증을 다음 대응으로 기호화했습니다. C: 사형 제도가 잔인하다 / J: 시행이 정당화된다 / R: 범죄발생률을 줄인다 / D: 사회의 품위를 떨어뜨린다. 원문 링크에서 문장을 읽고 기호화와 비교하세요.'});
h5('lang2','기호화 · 존재 논증','중급',['G','U','U->I','(I&~E)->~G'],'E',8,'3.2 (2)','~E를 가정하고 I와 연결하면 ~G가 도출됩니다.',{...derived,kind:'기호화 연습',note:'원문을 기호화한 연습입니다. G: 신은 그보다 더 큰 것이 생각될 수 없는 존재이다 / U: 우리는 ‘신’이라는 용어를 이해한다 / I: 신은 이해 속에 존재한다 / E: 신은 실재 속에 존재한다. 전제의 실제 참 여부가 아니라 논증의 형식을 연습합니다.'});
h5('lang3','기호화 · 악의 논증','심화',['(A&~W)->~B','E->(O&B)','V->(~W v ~A)','V'],'E->~A',8,'3.2 (3)','E에서 B를 얻으세요. A를 가정하면 ~W가 도출되고 ~B와 B가 충돌합니다.',{...derived,kind:'기호화 연습',note:'원문을 기호화했습니다. A: 신은 악을 막을 능력이 있다 / W: 신은 악을 막고자 한다 / B: 신은 전선하다 / E: 신은 존재한다 / O: 신은 전능하다 / V: 악이 존재한다. 전능과 악을 막을 능력은 별도 문자로 두며 추가 전제를 가정하지 않습니다.'});
own('1','첫걸음 · 모순 도입','기초',['Q','~Q'],'⊥','⊥를 입력하고 ⊥I, 근거 1,2를 선택하세요.');
own('2','첫걸음 · 이중부정 제거','기초',['~~P'],'P','수업의 ~E는 ~~P에서 P를 얻는 규칙입니다.');
own('3','첫걸음 · 선언 제거','기초',['P v Q','~P'],'Q','vE에 선언문과 ~P가 있는 두 줄을 인용하세요.');
own('4','첫걸음 · 쌍조건문 제거','기초',['P <-> Q','P'],'Q','<->E로 P → Q를 꺼낸 뒤 ->E를 적용하세요.');
own('5','기본 · 가정에서 부정으로','중급',['P->Q','~Q'],'~P','P를 가정해 Q를 얻고, ⊥I로 모순을 만든 뒤 ~I로 가정을 해제하세요.');
own('6','기본 · 중첩 조건문','중급',[],'P->(Q->P)','P를 가정한 뒤 Q를 가정하고 P를 반복하세요. 안쪽 가정부터 해제합니다.');
own('7','기본 · 두 범위로 동치','중급',['P->Q','Q->P'],'P<->Q','각 방향의 가정을 열고 결론을 얻은 뒤 닫아서 <->I에 두 범위를 인용해보세요.',{solution:[['P','가정',''],['Q','->E','1,3'],['','닫기',''],['Q','가정',''],['P','->E','2,5'],['','닫기',''],['P<->Q','<->I','3-4,5-6']]});
own('8','파생 · 조건문의 부정','중급',['~(P->Q)'],'P&~Q','파생 규칙 C로 조건문의 부정을 변환하세요.',derived);
own('9','파생 · 두 갈래의 같은 결론','중급',['A v B','A->C','B->C','C->D'],'D','AC로 C를 얻은 뒤 ->E로 D를 도출하세요.',derived);
own('10','파생 · 식 안의 변환','중급',['R->~(P v Q)'],'R->(~P&~Q)','DM은 전체 문장 속 한 부분에도 적용할 수 있습니다.',derived);
own('11','도전 · 배중률','심화',[],'P v ~P','~(P v ~P)를 가정하여 ~P를 얻고, 다시 P v ~P를 만들어 모순을 도출하세요.');
own('12','도전 · 분배와 후건 부정','심화',['P&(Q v R)','(P&Q)->S','(P&R)->S','~S'],'⊥','DR로 두 경우를 만든 뒤 AC를 적용하면 S가 나옵니다.',derived);
// Short hand-authored classroom solutions where derived rules are allowed.
const short={
'h41-t5':[['~(P v (P->Q))','가정',''],['P','가정',''],['P v (P->Q)','vI','2'],['⊥','⊥I','1,3'],['~P','~I','2-4'],['P','가정',''],['⊥','⊥I','5,6'],['~Q','가정',''],['⊥','R','7'],['~~Q','~I','8-9'],['Q','~E','10'],['P->Q','->I','6-11'],['P v (P->Q)','vI','12'],['⊥','⊥I','1,13'],['~~(P v (P->Q))','~I','1-14'],['P v (P->Q)','~E','15']],
'h41-v2':[['~((P->R) v (Q->R))','가정',''],['P','가정',''],['Q','가정',''],['P&Q','&I','3,4'],['R','->E','1,5'],['Q->R','->I','4-6'],['(P->R) v (Q->R)','vI','7'],['⊥','⊥I','2,8'],['~P','~I','3-9'],['P','가정',''],['⊥','⊥I','10,11'],['~R','가정',''],['⊥','R','12'],['~~R','~I','13-14'],['R','~E','15'],['P->R','->I','11-16'],['(P->R) v (Q->R)','vI','17'],['⊥','⊥I','2,18'],['~~((P->R) v (Q->R))','~I','2-19'],['(P->R) v (Q->R)','~E','20']],
'h4-extra1':[['B<->~C','<->I','1,2']],
'h5-e1':[['D&(E v (F->G))','DR','3'],['D','&E','4'],['C v D','vI','5'],['(C v D)->~B','<->E','2'],['~B','->E','6,7'],['A','vE','1,8']],
'h5-e2':[['~A->~C','CA','1,2'],['C','가정',''],['~~A','MT','3,4'],['A','~E','5'],['C->A','->I','4-6']],
'h5-e3':[['B->C','CA','3,4'],['~A','->E','2,5'],['(B->D)->(A v ~C)','->E','1,6'],['A v ~C','->E','7,3'],['~C','vE','8,6'],['~D','MT','4,9']],
'h5-e4':[['~A','가정',''],['C&B','->E','1,4'],['B','&E','5'],['~A->B','->I','4-6'],['~D','가정',''],['B&E','->E','2,8'],['B','&E','9'],['~D->B','->I','8-10'],['B','AC','3,7,11']],
'h5-t1':[['A->B','가정',''],['~B','가정',''],['~A','MT','1,2'],['A&C','가정',''],['A','&E','4'],['⊥','⊥I','3,5'],['~(A&C)','~I','4-6'],['~B->~(A&C)','->I','2-7'],['(A->B)->[~B->~(A&C)]','->I','1-8']],
'h5-t4':[['(A->C)&(B->C)','가정',''],['A->C','&E','1'],['B->C','&E','1'],['A v B','가정',''],['C','AC','2,3,4'],['(A v B)->C','->I','4-5'],['[(A->C)&(B->C)]->[(A v B)->C]','->I','1-6']],
'own-8':[['P&~Q','C','1']], 'own-9':[['C','AC','1,2,3'],['D','->E','4,5']], 'own-10':[['R->(~P&~Q)','DM','1']], 'own-12':[['(P&Q) v (P&R)','DR','1'],['S','AC','5,2,3'],['⊥','⊥I','4,6']]
};
function prune(p){
 if(p.solution.some(x=>x[1]==='닫기'))return;
 let s=L.initial(p.premises);for(const [f,r,refs] of p.solution)s=L.add(s,f,r,refs,p.allowed);
 const keep=new Set();function visit(n){if(keep.has(n))return;keep.add(n);let l=s.lines[n-1];for(const st of l.path)visit(st);for(const ref of l.refs.split(',').filter(Boolean))for(const id of ref.split('-'))visit(Number(id));}
 for(let i=1;i<=p.premises.length;i++)visit(i);visit(s.lines.length);
 const ids=[...keep].sort((a,b)=>a-b),map=new Map(ids.map((n,i)=>[n,i+1]));
 p.solution=ids.filter(n=>n>p.premises.length).map(n=>{let l=s.lines[n-1];return [format(l.a),l.rule,l.refs.replace(/\d+/g,x=>map.get(Number(x)))];});
}
const starterIds=new Set(['own-1','own-2','own-3','own-4']);
const sourceOrder={'핸드아웃 4':1,'추가 연습 4.1':2,'핸드아웃 5':3,'창작':4};
problems.sort((a,b)=>(starterIds.has(a.id)?0:sourceOrder[a.source])-(starterIds.has(b.id)?0:sourceOrder[b.source]));
for(const p of problems){p.category=starterIds.has(p.id)?'첫걸음':p.source;if(p.page)p.sourceFile??=p.source==='핸드아웃 4'?'handout-4.pdf':'handout-5.pdf';if(short[p.id])p.solution=short[p.id];if(!p.solution){let pr=new Proof(p);pr.prove(parse(p.goal));p.solution=pr.out}prune(p);let s=L.initial(p.premises);for(const [f,r,refs] of p.solution)s=r==='닫기'?L.close(s):L.add(s,f,r,refs,p.allowed);if(s.stack.length||!eq(s.lines.at(-1).a,parse(p.goal))||s.lines.at(-1).path.length)throw Error('Incomplete '+p.id);p.kind??=p.premises.length?'타당성':'필연적 참';console.log(p.id,p.solution.length)}
fs.writeFileSync('dist/problems.js','// Classroom edition: source page numbers refer to the supplied PDFs.\nconst PROBLEMS = '+JSON.stringify(problems,null,2)+';\nif(typeof module!=="undefined")module.exports=PROBLEMS;\n');
console.log('TOTAL',problems.length);
