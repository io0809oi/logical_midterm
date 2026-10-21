(function(){
'use strict';
const methods=[['natural','practiceNav','naturalPanel','rulesDialog','추론 규칙 안내'],['tree','treeNav','treePanel','treeRulesDialog','진리나무 규칙 안내'],['traditional','traditionalNav','traditionalPanel','tradRulesDialog','전통 논리 규칙 안내']];
const el=id=>document.getElementById(id);let active='natural';
function select(mode,focus=false){active=methods.some(m=>m[0]===mode)?mode:'natural';for(const [name,nav,panel] of methods){const on=name===active;el(panel).hidden=!on;el(nav).classList.toggle('active',on);el(nav).setAttribute('aria-selected',String(on));el(nav).tabIndex=on?0:-1;if(on&&focus)el(nav).focus();}el('rulesNav').querySelector('span').textContent=methods.find(m=>m[0]===active)[4];}
function navigate(name,focus=false){select(name,focus);window.history.replaceState(null,'','#'+name);}
for(const [name,nav] of methods)el(nav).onclick=()=>navigate(name);
el('methodTabs').onkeydown=e=>{if(!['ArrowLeft','ArrowRight','ArrowUp','ArrowDown','Home','End'].includes(e.key))return;e.preventDefault();const i=methods.findIndex(m=>m[0]===active),n=e.key==='Home'?0:e.key==='End'?2:(i+(['ArrowLeft','ArrowUp'].includes(e.key)?2:1))%3;navigate(methods[n][0],true);};
el('rulesNav').onclick=()=>el(methods.find(m=>m[0]===active)[3]).showModal();window.addEventListener('hashchange',()=>select(location.hash.slice(1)));select(location.hash.slice(1));
})();
