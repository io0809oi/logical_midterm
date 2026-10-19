'use strict';
const assert=require('node:assert/strict'),T=require('../dist/tree-logic.js'),L=require('../dist/logic.js'),P=require('../dist/tree-problems.js');
const assignment=(vars,n)=>Object.fromEntries(vars.map((v,i)=>[v,!!(n&(1<<i))]));
const ev=(a,m)=>typeof a==='string'?a==='⊥'?false:m[a]:({'¬':()=>!ev(a[1],m),'∧':()=>ev(a[1],m)&&ev(a[2],m),'∨':()=>ev(a[1],m)||ev(a[2],m),'→':()=>!ev(a[1],m)||ev(a[2],m),'↔':()=>ev(a[1],m)===ev(a[2],m)})[a[0]]();
assert.equal(P.length,19);assert.equal(new Set(P.map(p=>p.id)).size,19);
const expected=['closed','open','open','open','open','open','closed','open','closed','open','open','open','open','closed','open','closed','open','closed','open'];
for(const [i,p] of P.entries()){
 const sol=T.solve(p),vars=T.variables(p),fs=T.seeds(p).map(L.parse),models=[];
 for(let n=0;n<2**vars.length;n++){const m=assignment(vars,n);if(fs.every(a=>ev(a,m)))models.push(m);}
 const actual=T.status(sol.state);assert.equal(actual,models.length?'open':'closed',p.id);assert.equal(actual,expected[i],p.id);assert.deepEqual(T.replay(p,sol.actions),sol.state);
 const leaves=T.paths(sol.state).map(path=>T.branch(sol.state,path.at(-1).id));
 for(const b of leaves){if(b.node.open){assert.equal(T.pending(b).length,0);assert.equal(T.contradictions(b),null);const m=T.model(p,b);assert.ok(fs.every(a=>ev(a,m)),p.id+' countermodel');T.check(p,sol.state,'open',m);}else assert.ok(T.contradictions(b));}
 if(actual==='closed')T.check(p,sol.state,'closed');
 assert.throws(()=>T.check(p,sol.state,actual==='open'?'closed':'open',{}));
 for(const m of models)assert.ok(leaves.some(b=>b.node.open&&b.lines.every(l=>ev(l.a,m))),'tableau covers every satisfying assignment');
}
// Nine rules preserve truth, including compound operands.
for(const [rule,_,f] of T.rules){for(const formula of [f,f.replace(/A/g,'(P -> Q)').replace(/B/g,'(Q & ~R)')]){
 const a=L.parse(formula),d=T.decomposition(a),vs=T.atoms(a);assert.equal(d.rule,rule);
 for(let n=0;n<2**vs.length;n++){const m=assignment(vs,n);assert.equal(ev(a,m),d.branches.some(g=>g.every(x=>ev(x,m))),formula);}
}}
const p={kind:'consistency',formulas:['A v B','A -> C','~A']};let s=T.initial(p);
assert.throws(()=>T.apply(s,{type:'open',branch:1}),/모순|분해/);
assert.throws(()=>T.apply(s,{type:'expand',branch:1,line:2,rule:'->',left:'A',right:'C'}));
assert.throws(()=>T.apply(s,{type:'expand',branch:1,line:1,rule:'&',left:'A; B'}));
s=T.apply(s,{type:'expand',branch:1,line:1,rule:'v',left:'B',right:'A'});
const [b1,b2]=T.paths(s).map(path=>T.branch(s,path.at(-1).id));
const r2=b2.node.lines[0].id;
assert.throws(()=>T.apply(s,{type:'close',branch:b1.node.id,refs:'3,'+r2}),/같은 가지/);
assert.throws(()=>T.apply(s,{type:'expand',branch:b1.node.id,line:r2,rule:'~~',left:'A'}),/선택한 가지/);
assert.throws(()=>T.apply(s,{type:'expand',branch:b1.node.id,line:1,rule:'v',left:'A',right:'B'}),/이미/);
s=T.apply(s,{type:'close',branch:b2.node.id,refs:'3,'+r2});
assert.throws(()=>T.apply(s,{type:'open',branch:b2.node.id}),/이미/);
s=T.apply(s,{type:'expand',branch:b1.node.id,line:2,rule:'->',left:'~A',right:'C'});
// An ancestor expansion in one child must not mark it expanded in its sibling.
let t=T.initial({kind:'consistency',formulas:['A v B','C & D']});t=T.apply(t,{type:'expand',branch:1,line:1,rule:'v',left:'A',right:'B'});t=T.apply(t,{type:'expand',branch:2,line:2,rule:'&',left:'D; C'});assert.ok(T.pending(T.branch(t,3)).some(l=>l.id===2));assert.ok(!T.pending(T.branch(t,2)).some(l=>l.id===2));
// Reject incomplete group, extra branch, duplicate loss, malformed formula.
for(const action of [{left:'C'},{left:'C; D',right:'C'},{left:'C; C'},{left:'(C; D'}])assert.throws(()=>T.apply(t,{type:'expand',branch:3,line:2,rule:'&',...action}));
const solved=T.solve(P[1]).state;assert.throws(()=>T.check(P[1],solved,'open',{}));assert.throws(()=>T.check(P[1],solved,'open',{A:true,B:true,D:false}));
console.log('Truth trees: 19 problems, truth-table equivalence, all 9 rules, branch scope, closure, countermodels, and replay passed.');
