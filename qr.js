/* Генератор QR-кода без зависимостей (режим «байты», коррекция ошибок M, версии 1–10, до 213 байт).
   qrMatrix(text) -> массив строк из 0/1. Кодировка текста: UTF-8. */
function qrMatrix(text,forceMask){
  const data=Array.from(new TextEncoder().encode(text));
  // ── параметры версий для уровня M: [всего слов данных, ECC на блок, блоков группы 1, слов в блоке 1, блоков группы 2, слов в блоке 2]
  const VER=[null,[16,10,1,16,0,0],[28,16,1,28,0,0],[44,26,1,44,0,0],[64,18,2,32,0,0],[86,24,2,43,0,0],
    [108,16,4,27,0,0],[124,18,4,31,0,0],[154,22,2,38,2,39],[182,22,3,36,2,37],[216,26,4,43,1,44]];
  const ALIGN=[null,[],[6,18],[6,22],[6,26],[6,30],[6,34],[6,22,38],[6,24,42],[6,26,46],[6,28,50]];
  let v=1;
  for(;v<=10;v++){const cc=v<=9?8:16;if(4+cc+data.length*8<=VER[v][0]*8)break;}
  if(v>10)throw new Error('Текст слишком длинный для QR');
  const [total,eccLen,g1n,g1len,g2n,g2len]=VER[v];
  // ── поток битов: режим 0100, длина, данные, терминатор, добивка 0xEC/0x11
  const bits=[];const put=(val,n)=>{for(let i=n-1;i>=0;i--)bits.push((val>>i)&1);};
  put(4,4);put(data.length,v<=9?8:16);data.forEach(b=>put(b,8));
  const cap=total*8;put(0,Math.min(4,cap-bits.length));while(bits.length%8)bits.push(0);
  const cw=[];for(let i=0;i<bits.length;i+=8){let x=0;for(let j=0;j<8;j++)x=(x<<1)|bits[i+j];cw.push(x);}
  for(let p=0;cw.length<total;p++)cw.push(p%2?0x11:0xEC);
  // ── Рид–Соломон над GF(256), полином 0x11D
  const EXP=new Array(512),LOG=new Array(256);
  for(let i=0,x=1;i<255;i++){EXP[i]=x;LOG[x]=i;x<<=1;if(x&256)x^=0x11D;}
  for(let i=255;i<512;i++)EXP[i]=EXP[i-255];
  const mul=(a,b)=>(a&&b)?EXP[LOG[a]+LOG[b]]:0;
  const gen=[1];
  for(let i=0;i<eccLen;i++){const g=new Array(gen.length+1).fill(0);
    for(let j=0;j<gen.length;j++){g[j]^=gen[j];g[j+1]^=mul(gen[j],EXP[i]);}gen.length=0;gen.push(...g);}
  const rs=block=>{const r=new Array(eccLen).fill(0);
    for(const b of block){const f=b^r[0];r.shift();r.push(0);if(f)for(let i=0;i<eccLen;i++)r[i]^=mul(gen[i+1],f);}return r;};
  const blocks=[];let o=0;
  for(let i=0;i<g1n+g2n;i++){const len=i<g1n?g1len:g2len;blocks.push(cw.slice(o,o+len));o+=len;}
  const eccs=blocks.map(rs);
  const out=[];const maxLen=Math.max(g1len,g2len||0);
  for(let i=0;i<maxLen;i++)blocks.forEach(b=>{if(i<b.length)out.push(b[i]);});
  for(let i=0;i<eccLen;i++)eccs.forEach(e=>out.push(e[i]));
  const finalBits=[];out.forEach(b=>{for(let i=7;i>=0;i--)finalBits.push((b>>i)&1);});
  // ── матрица
  const N=17+4*v;
  const M=Array.from({length:N},()=>new Array(N).fill(0));      // значение
  const F=Array.from({length:N},()=>new Array(N).fill(false));  // занято служебным узором
  const set=(r,c,val)=>{if(r>=0&&r<N&&c>=0&&c<N){M[r][c]=val?1:0;F[r][c]=true;}};
  const finder=(r,c)=>{for(let i=-1;i<=7;i++)for(let j=-1;j<=7;j++){
    const on=(i>=0&&i<=6&&(j===0||j===6))||(j>=0&&j<=6&&(i===0||i===6))||(i>=2&&i<=4&&j>=2&&j<=4);set(r+i,c+j,on);}};
  finder(0,0);finder(0,N-7);finder(N-7,0);
  for(let i=8;i<N-8;i++){set(6,i,i%2===0);set(i,6,i%2===0);}
  const al=ALIGN[v];
  for(const r of al)for(const c of al){
    if((r===6&&c===6)||(r===6&&c===al[al.length-1])||(c===6&&r===al[al.length-1]))continue;
    for(let i=-2;i<=2;i++)for(let j=-2;j<=2;j++)set(r+i,c+j,Math.max(Math.abs(i),Math.abs(j))!==1);}
  set(N-8,8,true);                                              // тёмный модуль
  const reserve=()=>{for(let i=0;i<9;i++){if(!F[8][i])set(8,i,0);if(!F[i][8])set(i,8,0);}
    for(let i=0;i<8;i++){set(8,N-1-i,0);set(N-1-i,8,0);}set(N-8,8,true);};
  reserve();
  if(v>=7){let x=v;for(let i=0;i<12;i++)x=(x<<1)^(((x>>11)&1)?0x1F25:0);const info=(v<<12)|x;
    for(let i=0;i<18;i++){const b=(info>>i)&1;set(Math.floor(i/3),N-11+(i%3),b);set(N-11+(i%3),Math.floor(i/3),b);}}
  // ── размещение данных зигзагом
  const place=[];let up=true;
  for(let c=N-1;c>0;c-=2){if(c===6)c--;
    for(let k=0;k<N;k++){const r=up?N-1-k:k;for(let j=0;j<2;j++){const cc=c-j;if(!F[r][cc])place.push([r,cc]);}}up=!up;}
  const MASKS=[(r,c)=>(r+c)%2===0,(r,c)=>r%2===0,(r,c)=>c%3===0,(r,c)=>(r+c)%3===0,
    (r,c)=>(Math.floor(r/2)+Math.floor(c/3))%2===0,(r,c)=>((r*c)%2+(r*c)%3)===0,
    (r,c)=>(((r*c)%2+(r*c)%3)%2)===0,(r,c)=>(((r+c)%2+(r*c)%3)%2)===0];
  const fmt=mask=>{const d=(0<<3)|mask;let x=d;for(let i=0;i<10;i++)x=(x<<1)^(((x>>9)&1)?0x537:0);return(((d<<10)|x)^0x5412);};
  const build=mask=>{
    const A=M.map(r=>r.slice());
    place.forEach(([r,c],i)=>{const bit=i<finalBits.length?finalBits[i]:0;A[r][c]=bit^(MASKS[mask](r,c)?1:0);});
    const f=fmt(mask),fb=i=>(f>>i)&1;
    for(let i=0;i<15;i++){                                       // две копии 15-битного кода формата
      const bit=fb(i);
      if(i<6)A[i][8]=bit;else if(i<8)A[i+1][8]=bit;else A[N-15+i][8]=bit;
      if(i<8)A[8][N-1-i]=bit;else if(i<9)A[8][15-i-1+1]=bit;else A[8][15-i-1]=bit;}
    A[N-8][8]=1;return A;};
  const penalty=A=>{let p=0;
    for(let k=0;k<2;k++)for(let i=0;i<N;i++){let run=1;for(let j=1;j<N;j++){
      const a=k?A[j][i]:A[i][j],b=k?A[j-1][i]:A[i][j-1];if(a===b){run++;if(run===5)p+=3;else if(run>5)p++;}else run=1;}}
    for(let i=0;i<N-1;i++)for(let j=0;j<N-1;j++){const s=A[i][j];if(s===A[i][j+1]&&s===A[i+1][j]&&s===A[i+1][j+1])p+=3;}
    const pat=[1,0,1,1,1,0,1,0,0,0,0],pat2=pat.slice().reverse();
    for(let i=0;i<N;i++)for(let j=0;j<=N-11;j++){let a=true,b=true,c=true,d=true;
      for(let k=0;k<11;k++){if(A[i][j+k]!==pat[k])a=false;if(A[i][j+k]!==pat2[k])b=false;
        if(A[j+k][i]!==pat[k])c=false;if(A[j+k][i]!==pat2[k])d=false;}
      if(a)p+=40;if(b)p+=40;if(c)p+=40;if(d)p+=40;}
    let dark=0;for(const r of A)for(const x of r)dark+=x;
    p+=Math.floor(Math.abs(dark*100/(N*N)-50)/5)*10;return p;};
  let best=null,bp=1e9;
  for(let m=0;m<8;m++){if(forceMask!==undefined&&m!==forceMask)continue;const A=build(m),p=penalty(A);if(p<bp){bp=p;best=A;}}
  return best;
}
/* Нарисовать QR на <canvas>: тихая зона 4 модуля, масштаб подбирается под размер. */
function qrDraw(canvas,text,px){
  const m=qrMatrix(text),n=m.length,q=4,scale=Math.max(2,Math.floor(px/(n+2*q)));
  canvas.width=canvas.height=(n+2*q)*scale;const c=canvas.getContext('2d');
  c.fillStyle='#fff';c.fillRect(0,0,canvas.width,canvas.height);c.fillStyle='#000';
  for(let r=0;r<n;r++)for(let k=0;k<n;k++)if(m[r][k])c.fillRect((k+q)*scale,(r+q)*scale,scale,scale);
}
if(typeof module!=='undefined')module.exports={qrMatrix,qrDraw};
