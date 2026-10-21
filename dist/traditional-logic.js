(function(root){
'use strict';
const regions=Array.from({length:8},(_,i)=>i),inside=(r,t)=>!!(r&(1<<t));
const rows=[
 ['포유류와 고래',['고래','포유류','동물'],['모든 포유류는 동물이다.','모든 고래는 포유류이다.'],'모든 고래는 동물이다.',[['A',1,2],['A',0,1]],['A',0,2],'두 전칭 전제가 비워 놓는 영역을 함께 확인하세요.'],
 ['척추동물과 새',['새','척추동물','동물'],['모든 척추동물은 동물이다.','어떤 새는 척추동물이다.'],'어떤 새는 동물이다.',[['A',1,2],['I',0,1]],['I',0,2],'전칭 전제를 먼저 표시하면 특칭 전제의 X가 갈 곳이 좁아집니다.'],
 ['고양이와 야행성',['고양이','동물','야행성인 것'],['모든 고양이는 동물이다.','어떤 동물은 야행성이다.'],'어떤 고양이는 야행성이다.',[['A',0,1],['I',1,2]],['I',0,2],'야행성인 동물이 반드시 고양이인지 생각해 보세요.'],
 ['운동선수와 프로게이머',['프로게이머','운동선수','게으른 사람'],['어떤 운동선수도 게으르지 않다.','모든 프로게이머는 운동선수이다.'],'어떤 프로게이머도 게으르지 않다.',[['E',1,2],['A',0,1]],['E',0,2],'“어떤 …도 …아니다”는 전칭부정 E입니다.'],
 ['영웅과 군인',['군인','용감한 사람','영웅'],['모든 영웅은 용감하다.','어떤 군인은 용감하다.'],'어떤 군인은 영웅이다.',[['A',2,1],['I',0,1]],['I',0,2],'용감한 사람 중 영웅이 아닌 사람도 가능한지 확인하세요.'],
 ['포유류와 뱀',['뱀','파충류','포유류'],['어떤 포유류도 파충류가 아니다.','모든 뱀은 파충류이다.'],'어떤 뱀도 포유류가 아니다.',[['E',2,1],['A',0,1]],['E',0,2],'두 집합이 겹치지 않는다는 전제는 교집합 전체를 비웁니다.'],
 ['정사각형과 존재 함축',['마름모','정사각형','직사각형'],['모든 정사각형은 직사각형이다.','모든 정사각형은 마름모이다.'],'어떤 마름모는 직사각형이다.',[['A',1,2],['A',1,0]],['I',0,2],'불의 해석에서는 정사각형이 하나도 없는 경우도 전제들을 참으로 만듭니다. 두 해석을 각각 풀어 보세요.'],
 ['고래와 멸종 위기종',['멸종 위기종','고래','포유류'],['모든 고래는 포유류이다.','어떤 고래는 멸종 위기종이다.'],'어떤 멸종 위기종은 포유류이다.',[['A',1,2],['I',1,0]],['I',0,2],'특칭 전제의 X에 전칭 전제의 제한을 적용하세요.'],
 ['오직 철학자만 현명하다',['과학자','현명한 사람','철학자'],['오직 철학자만 현명하다.','어떤 과학자는 현명하다.'],'어떤 과학자는 철학자이다.',[['A',1,2],['I',0,1]],['I',0,2],'“오직 B만 A이다”는 “모든 A는 B이다”로 번역합니다.'],
 ['저 산의 연기와 불',['저 산인 장소','연기가 있는 장소','불이 있는 장소'],['연기가 있는 곳엔 어디든 불이 있다.','저 산엔 연기가 있다.'],'저 산엔 불이 있다.',[['A',1,2],['A',0,1],['I',0,0]],['A',0,2],'“저 산”은 존재하는 특정 장소입니다. 그 장소를 나타내는 X가 어디에 놓이는지 보세요.']
];
const problems=rows.map(([title,terms,premiseText,goalText,premises,goal,hint],i)=>({id:'traditional2-'+(i+1),number:i+1,title,terms,premiseText,goalText,premises,goal,hint,page:i===9?20:19,category:i<4?'기초':i<8?'심화':'자연어 번역',modes:i===6?['boole','aristotle']:['boole'],singleton:i===9?0:null}));
function occupied(model,r){return !!(model&(1<<r));}
function satisfies(f,m,existential=false){const [k,s,p]=f,has=predicate=>regions.some(r=>occupied(m,r)&&predicate(r)),subject=r=>inside(r,s),both=r=>subject(r)&&inside(r,p),outside=r=>subject(r)&&!inside(r,p);if(k==='I')return has(both);if(k==='O')return has(outside);return (k==='A'?!has(outside):!has(both))&&(!existential||has(subject));}
function universe(p,m){return m>0&&(p.singleton===null||regions.filter(r=>occupied(m,r)&&inside(r,p.singleton)).length===1);}
function models(p,mode='boole'){return Array.from({length:255},(_,i)=>i+1).filter(m=>universe(p,m)&&p.premises.every(f=>satisfies(f,m,mode==='aristotle')));}
function countermodels(p,mode='boole'){return models(p,mode).filter(m=>!satisfies(p.goal,m,mode==='aristotle'));}
function canonical(p,mode='boole'){const shaded=new Set(),groups=[];for(const [k,s,t] of p.premises){const rs=regions.filter(r=>inside(r,s)&&(k==='A'||k==='O'?!inside(r,t):inside(r,t)));if(k==='A'||k==='E'){rs.forEach(r=>shaded.add(r));if(mode==='aristotle')groups.push(regions.filter(r=>inside(r,s)));}else groups.push(rs);}return {shaded:[...shaded].sort(),groups:groups.map(g=>g.filter(r=>!shaded.has(r))).filter((g,i,a)=>a.findIndex(z=>JSON.stringify(z)===JSON.stringify(g))===i)};}
function diagramModels(p,d){return Array.from({length:255},(_,i)=>i+1).filter(m=>universe(p,m)&&d.shaded.every(r=>!occupied(m,r))&&d.groups.every(g=>g.some(r=>occupied(m,r))));}
function checkDiagram(p,mode,d){if(!Array.isArray(d.shaded)||!Array.isArray(d.groups)||d.shaded.some(r=>!regions.includes(r))||d.groups.some(g=>!Array.isArray(g)||!g.length||g.some(r=>!regions.includes(r))))throw Error('음영과 X 표시를 확인하세요.');const target=models(p,mode),actual=diagramModels(p,d);if(JSON.stringify(target)!==JSON.stringify(actual)){if(actual.some(m=>!target.includes(m)))throw Error('전제의 조건이 아직 빠져 있습니다. 비어 있어야 할 영역과 반드시 필요한 X를 확인하세요.');throw Error('전제보다 강한 조건을 표시했습니다. 필요 없는 음영이나 X, 한 영역으로 너무 좁힌 X를 확인하세요.');}return true;}
function check(p,mode,d,verdict,model,translation){if(!p.modes.includes(mode))throw Error('이 문제에서 제공하는 해석을 선택하세요.');if(p.number===9&&(translation?.type!=='A'||translation?.direction!=='wise-philosopher'))throw Error('“오직 철학자만 현명하다”의 양과 방향을 다시 확인하세요.');checkDiagram(p,mode,d);const cs=countermodels(p,mode),answer=cs.length?'invalid':'valid';if(verdict!==answer)throw Error('전제의 표시만으로 결론이 반드시 성립하는지 다시 확인하세요.');if(answer==='invalid'&&!cs.includes(model))throw Error('반례는 전제가 모두 참이고 결론이 거짓인 경우여야 합니다. 존재하는 대상을 영역에 배치하세요.');return answer;}
function regionLabel(p,r){return r===0?'세 집합 모두 바깥':p.terms.map((t,i)=>t+(inside(r,i)?' O':' X')).join(' · ');}
const api={problems,regions,inside,occupied,satisfies,universe,models,countermodels,canonical,diagramModels,checkDiagram,check,regionLabel};if(typeof module!=='undefined')module.exports=api;else root.Traditional=api;
})(globalThis);
