(function(root){
'use strict';
const L=typeof module!=='undefined'?require('./logic.js'):root.Logic;
const {parse,eq,op,neg,contra,format}=L;
const rules=[['&','연언','A & B','A; B',''],['~v','부정된 선언','~(A v B)','~A; ~B',''],['~->','부정된 조건문','~(A -> B)','A; ~B',''],['~~','이중 부정','~~A','A',''],['~&','부정된 연언','~(A & B)','~A','~B'],['v','선언','A v B','A','B'],['->','조건문','A -> B','~A','B'],['<->','쌍조건문','A <-> B','A; B','~A; ~B'],['~<->','부정된 쌍조건문','~(A <-> B)','A; ~B','~A; B']];
function decomposition(a){
 if(typeof a==='string')return null;
 const [k,x,y]=a;
 if(k==='∧')return {rule:'&',branches:[[x,y]]};
 if(k==='∨')return {rule:'v',branches:[[x],[y]]};
 if(k==='→')return {rule:'->',branches:[[neg(x)],[y]]};
 if(k==='↔')return {rule:'<->',branches:[[x,y],[neg(x),neg(y)]]};
 if(k==='¬'&&Array.isArray(x)){
  const [j,b,c]=x;
  if(j==='¬')return {rule:'~~',branches:[[b]]};
  if(j==='∨')return {rule:'~v',branches:[[neg(b),neg(c)]]};
  if(j==='→')return {rule:'~->',branches:[[b,neg(c)]]};
  if(j==='∧')return {rule:'~&',branches:[[neg(b)],[neg(c)]]};
  if(j==='↔')return {rule:'~<->',branches:[[b,neg(c)],[neg(b),c]]};
 }
 return null;
}
function seeds(p){if(p.kind==='consistency')return p.formulas;if(p.kind==='validity')return [...p.premises,'~('+p.goal+')'];if(p.kind==='tautology')return ['~('+p.formula+')'];if(p.kind==='contradiction')return [p.formula];return ['~(('+p.formulas[0]+') <-> ('+p.formulas[1]+'))'];}
function initial(p){return {nextNode:2,nextLine:seeds(p).length+1,root:{id:1,lines:seeds(p).map((f,i)=>({id:i+1,a:parse(f),source:null,rule:'SM'})),used:[],children:[],closed:null,open:false}};}
function paths(s){const out=[];function walk(n,parents){const path=[...parents,n];if(!n.children.length)out.push(path);else n.children.forEach(c=>walk(c,path));}walk(s.root,[]);return out;}
function branch(s,id){const path=paths(s).find(p=>p.at(-1).id===Number(id));if(!path)throw Error('끝 가지를 선택하세요.');return {path,node:path.at(-1),lines:path.flatMap(n=>n.lines),used:new Set(path.flatMap(n=>n.used))};}
function contradictions(b){for(let i=0;i<b.lines.length;i++){if(b.lines[i].a==='⊥')return [b.lines[i].id];for(let j=i+1;j<b.lines.length;j++)if(contra(b.lines[i].a,b.lines[j].a))return [b.lines[i].id,b.lines[j].id];}return null;}
function pending(b){return b.lines.filter(l=>!b.used.has(l.id)&&decomposition(l.a));}
function parseGroup(s){return String(s||'').split(/[;\n]+/).map(x=>x.trim()).filter(Boolean).map(parse);}
function sameGroup(a,b){if(a.length!==b.length)return false;const copy=[...b];for(const f of a){const i=copy.findIndex(g=>eq(f,g));if(i<0)return false;copy.splice(i,1);}return true;}
function apply(state,action){const s=JSON.parse(JSON.stringify(state)),b=branch(s,action.branch),n=b.node;if(n.closed||n.open)throw Error('이미 판정한 가지입니다. 되돌리기로 다시 열 수 있습니다.');
 if(action.type==='expand'){
  const line=b.lines.find(l=>l.id===Number(action.line));if(!line)throw Error('선택한 가지 위의 줄만 참조할 수 있습니다.');
  if(b.used.has(line.id))throw Error('이 가지에서는 이미 분해한 문장입니다.');const d=decomposition(line.a);if(!d)throw Error('단순 문장과 그 부정은 더 분해하지 않습니다.');
  if(action.rule!==d.rule)throw Error('문장의 가장 바깥쪽 기호에 맞는 분해 규칙을 선택하세요.');
  const left=parseGroup(action.left),right=parseGroup(action.right),groups=right.length?[left,right]:[left];
  const okay=groups.length===d.branches.length&&(d.branches.length===1?sameGroup(groups[0],d.branches[0]):(sameGroup(groups[0],d.branches[0])&&sameGroup(groups[1],d.branches[1]))||(sameGroup(groups[0],d.branches[1])&&sameGroup(groups[1],d.branches[0])));
  if(!okay)throw Error(d.branches.length===1?'같은 가지에 필요한 문장을 모두 입력하세요. 문장 사이는 세미콜론(;)으로 구분하고 오른쪽 가지는 비우세요.':'두 가지의 문장을 확인하세요. 같은 가지에 놓을 문장은 세미콜론(;)으로 구분합니다.');
  n.used.push(line.id);const lines=g=>g.map(a=>({id:s.nextLine++,a,source:line.id,rule:d.rule}));
  if(groups.length===1)n.lines.push(...lines(groups[0]));else n.children=groups.map(g=>({id:s.nextNode++,lines:lines(g),used:[],children:[],closed:null,open:false}));
 }else if(action.type==='close'){
  const refs=String(action.refs||'').split(',').map(x=>Number(x.trim()));const ls=refs.map(id=>b.lines.find(l=>l.id===id));
  if(!ls.every(Boolean)||!((ls.length===1&&ls[0].a==='⊥')||(ls.length===2&&contra(ls[0].a,ls[1].a))))throw Error('같은 가지 위에서 서로 모순인 두 줄을 쉼표로 입력하세요. 예: 2,7');
  n.closed=refs;
 }else if(action.type==='open'){
  if(contradictions(b))throw Error('이 가지에는 모순이 있습니다. 모순인 두 줄로 가지를 닫으세요.');
  if(pending(b).length)throw Error('아직 분해하지 않은 복합 문장이 있습니다. 모두 분해한 뒤 열린 가지로 표시하세요.');
  n.open=true;
 }else throw Error('알 수 없는 작업입니다.');
 return s;
}
function replay(p,actions){if(!Array.isArray(actions)||actions.length>1500)throw Error('저장된 풀이를 읽을 수 없습니다.');return actions.reduce(apply,initial(p));}
function atoms(a,set=new Set()){if(typeof a==='string'){if(a!=='⊥')set.add(a);}else a.slice(1).forEach(x=>atoms(x,set));return [...set].sort();}
function variables(p){const set=new Set();seeds(p).forEach(f=>atoms(parse(f),set));return [...set].sort();}
function evaluate(a,m){if(typeof a==='string')return a==='⊥'?false:!!m[a];const x=evaluate(a[1],m);if(a[0]==='¬')return !x;const y=evaluate(a[2],m);return a[0]==='∧'?x&&y:a[0]==='∨'?x||y:a[0]==='→'?!x||y:x===y;}
function model(p,b){const m=Object.fromEntries(variables(p).map(v=>[v,false]));for(const l of b.lines){if(typeof l.a==='string'&&l.a!=='⊥')m[l.a]=true;else if(op(l.a,'¬')&&typeof l.a[1]==='string')m[l.a[1]]=false;}return m;}
function status(s){const bs=paths(s).map(p=>branch(s,p.at(-1).id));return bs.every(b=>b.node.closed)?'closed':bs.some(b=>b.node.open)?'open':'unfinished';}
function labels(p){return p.kind==='consistency'?['일관적','비일관적']:p.kind==='validity'?['타당하지 않음','타당함']:p.kind==='tautology'?['논리적 참이 아님','논리적 참']:p.kind==='contradiction'?['논리적 거짓이 아님','논리적 거짓']:['동치가 아님','동치'];}
function check(p,s,answer,m){const st=status(s);if(st==='unfinished')throw Error('모든 가지를 닫거나, 완전히 분해한 열린 가지를 하나 이상 표시하세요.');if(answer!==st)throw Error('열린 가지와 닫힌 나무가 의미하는 판정을 다시 확인하세요.');if(st==='open'){
 if(!m||variables(p).some(v=>typeof m[v]!=='boolean'))throw Error('각 명제 문자의 진리값을 선택하세요.');
 const matches=paths(s).map(path=>branch(s,path.at(-1).id)).some(b=>b.node.open&&b.lines.every(l=>evaluate(l.a,m)));
 if(!matches||!seeds(p).every(f=>evaluate(parse(f),m)))throw Error('이 진리값은 표시한 열린 가지를 만족하지 않습니다. 가지 위의 단순 문장과 부정을 확인하세요.');
 }return labels(p)[st==='open'?0:1];}
function suggest(s){for(const path of paths(s)){const b=branch(s,path.at(-1).id);if(b.node.closed||b.node.open)continue;const c=contradictions(b);if(c)return {type:'close',branch:b.node.id,refs:c.join(',')};const list=pending(b).sort((a,z)=>decomposition(a.a).branches.length-decomposition(z.a).branches.length);if(!list.length)return {type:'open',branch:b.node.id};const l=list[0],d=decomposition(l.a);return {type:'expand',branch:b.node.id,line:l.id,rule:d.rule,left:d.branches[0].map(format).join('; '),right:(d.branches[1]||[]).map(format).join('; ')};}return null;}
function solve(p){let s=initial(p),actions=[],a;while((a=suggest(s))){if(actions.length>1000)throw Error('풀이 단계 한도를 초과했습니다.');actions.push(a);s=apply(s,a);}return {state:s,actions};}
const api={rules,decomposition,seeds,initial,paths,branch,contradictions,pending,apply,replay,atoms,variables,evaluate,model,status,labels,check,suggest,solve};if(typeof module!=='undefined')module.exports=api;else root.TruthTree=api;
})(globalThis);
