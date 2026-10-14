const assert=require('node:assert/strict');const L=require('../dist/logic.js');
for(const p of L.problems){let s=L.initial(p.premises);for(const [f,r,refs] of p.solution)s=r==='닫기'?L.close(s):L.add(s,f,r,refs);assert.equal(s.stack.length,0,p.title);assert(L.eq(s.lines.at(-1).a,L.parse(p.goal)),p.title)}
assert(L.eq(L.parse('P -> Q -> R'),L.parse('P → (Q → R)')));
assert(L.eq(L.parse('~P & Q | R'),L.parse('(¬P ∧ Q) ∨ R')));
assert.throws(()=>L.parse('(P → Q'));
let s=L.initial(['P → Q','P']);assert.throws(()=>L.add(s,'R','→E','1,2'));assert.throws(()=>L.add(s,'Q','→E','1,3'));assert.throws(()=>L.add(s,'Q','→E','1'));s=L.add(s,'Q','→E','2,1');
s=L.initial([]);s=L.add(s,'P','가정');s=L.add(s,'P','R','1');s=L.add(s,'P → P','→I','1-2');assert.throws(()=>L.add(s,'P','R','1'));assert.throws(()=>L.add(s,'P','R','2'));
s=L.initial([]);s=L.add(s,'P','가정');s=L.add(s,'Q','가정');assert.throws(()=>L.add(s,'P → Q','→I','1-2'));s=L.add(s,'P','R','1');s=L.add(s,'Q → P','→I','2-3');s=L.add(s,'P → (Q → P)','→I','1-4');assert.equal(s.stack.length,0);
s=L.initial(['P ∨ Q']);s=L.add(s,'P','가정');s=L.add(s,'P','R','2');s=L.close(s);s=L.add(s,'Q','가정');s=L.add(s,'Q','R','4');s=L.close(s);assert.throws(()=>L.add(s,'P','∨E','1,2-3,4-5'));assert.throws(()=>L.add(s,'P','∨E','1,2-5,4-5'));assert.throws(()=>L.add(s,'P','R','3'));
s=L.initial(['P','¬P']);s=L.add(s,'⊥','¬E','1,2');s=L.add(s,'Q','⊥E','3');assert(L.eq(s.lines.at(-1).a,L.parse('Q')));
console.log('PASS: all 12 example proofs; precedence; invalid inference; references; nested/discharged scopes; disjunction branches; contradiction.');
