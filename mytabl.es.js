/*! MyTables v0.0.9.1 | (c) 2014
//@ http://mytabl.es
*/

(function ($) {

	// ---------------------- Arbitrary Precision Math
	// badd(a,b), bsub(a,b), bmul(a,b), bdiv(a,b), bmod(a,b),
	// brshift(a), beq(a,b)

	// set the base... 32bit cpu -> bs=16, 64bit -> bs=32
	// bm is the mask, bs is the shift
	//bm=0xf; bs=4;  // low base useful for testing if digits handled ok
	bs=28;
	bx2=1<<bs; bm=bx2-1; bx=bx2>>1; bd=bs>>1; bdm=(1 << bd) -1
	log2=Math.log(2)

	function badd(a,b) { // binary add
		var al=a.length, bl=b.length
		if(al < bl) return badd(b,a)
		var c=0, r=[], n=0
		for(; n<bl; n++) {
		c+=a[n]+b[n]
		r[n]=c & bm
		c>>>=bs
		}
		for(; n<al; n++) {
		c+=a[n]
		r[n]=c & bm
		c>>>=bs
		}
		if(c) r[n]=c
		return r
	}
	
	function beq(a,b) { // returns 1 if a == b
		if(a.length != b.length) return 0
		for(var n=a.length-1; n>=0; n--)
		if(a[n] != b[n]) return 0
		return 1
	}
	
	function bsub(a,b) { // binary subtract
		var al=a.length, bl=b.length, c=0, r=[]
		if(bl > al) {return []}
		if(bl == al) {
		if(b[bl-1] > a[bl-1]) return []
		if(bl==1) return [a[0]-b[0]]
		}
		for(var n=0; n<bl; n++) {
		c+=a[n]-b[n]
		r[n]=c & bm
		c>>=bs
		}
		for(;n<al; n++) {
		c+=a[n]
		r[n]=c & bm
		c>>=bs
		}
		if(c) {return []}
		if(r[n-1]) return r
		while(n>1 && r[n-1]==0) n--;
		return r.slice(0,n)
	}
	
	function bmul(a,b) { // binary multiply
		b=b.concat([0])
		var al=a.length, bl=b.length, r=[], n,nn,aa, c, m
		var g,gg,h,hh, ghhb

		for(n=al+bl; n>=0; n--) r[n]=0
		for(n=0; n<al; n++) {
		if(aa=a[n]) {
		c=0
		hh=aa>>bd; h=aa & bdm
		m=n
		for(nn=0; nn<bl; nn++, m++) {
		g = b[nn]; gg=g>>bd; g=g & bdm
		//(gg*2^15 + g) * (hh*2^15 + h) = (gghh*2^30 + (ghh+hgg)*2^15 +hg)
		ghh = g * hh + h * gg
		ghhb= ghh >> bd; ghh &= bdm
		c += r[m] + h * g + (ghh << bd)
		r[m] = c & bm
		c = (c >> bs) + gg * hh + ghhb
		}
		}
		}
		n=r.length
		if(r[n-1]) return r
		while(n>1 && r[n-1]==0) n--;
		return r.slice(0,n)
	}

	function blshift(a,b) {
		var n, c=0, r=[]
		for(n=0; n<a.length; n++) {
		c|= (a[n]<<b) 
		r[n]= c & bm
		c>>=bs
		}
		if(c) r[n]=c
		return r
	}
	
	function brshift(a) {
		var c=0,n,cc, r=[]
		for(n=a.length-1; n>=0; n--) {
		cc=a[n]; c<<=bs
		r[n]=(cc | c)>>1
		c=cc & 1
		}
		while(r.length > 1 && r[r.length-1]==0) {
		r=r.slice(0,-1)
		}
		this.a=r; this.c=c
		return this
	}
	
	function zeros(n) {var r=[]; while(n-->0) r[n]=0; return r}
	
	function toppart(x,start,len) { var n=0
		while(start >= 0 && len-->0) n=n*bx2+x[start--]
		return n
		}
		//14.20 Algorithm Multiple-precision division from HAC
		function bdiv(x,y) {
		var n=x.length-1, t=y.length-1, nmt=n-t
		// trivial cases; x < y
		if(n < t || n==t && (x[n]<y[n] || n>0 && x[n]==y[n] && x[n-1]<y[n-1])) {
		this.q=[0]; this.mod=x; return this
		}
		// trivial cases; q < 4
		if(n==t && toppart(x,t,2)/toppart(y,t,2) <4) {
		var q=0, xx
		for(;;) {
		xx=bsub(x,y)
		if(xx.length==0) break
		x=xx; q++
		}
		this.q=[q]; this.mod=x; return this
		}
		var shift, shift2
		// normalize
		shift2=Math.floor(Math.log(y[t])/log2)+1
		shift=bs-shift2
		if(shift) {
		x=x.concat(); y=y.concat()
		for(i=t; i>0; i--) y[i]=((y[i]<<shift) & bm) | (y[i-1] >> shift2); y[0]=(y[0]<<shift) & bm
		if(x[n] & ((bm <<shift2) & bm)) { x[++n]=0; nmt++; }
		for(i=n; i>0; i--) x[i]=((x[i]<<shift) & bm) | (x[i-1] >> shift2); x[0]=(x[0]<<shift) & bm
		}
		var i, j, x2, y2,q=zeros(nmt+1)

		y2=zeros(nmt).concat(y)
		for(;;) {
		x2=bsub(x,y2)
		if(x2.length==0) break
		q[nmt]++
		x=x2
		}
		var yt=y[t], top=toppart(y,t,2)
		for(i=n; i>t; i--) {
		m=i-t-1
		if(i >= x.length)
		q[m]=1
		else if(x[i] == yt)
		q[m]=bm
		else
		q[m]=Math.floor(toppart(x,i,2)/yt)

		topx=toppart(x,i,3)
		while(q[m] * top > topx)
		q[m]--
		//x-=q[m]*y*b^m
		y2=y2.slice(1)
		x2=bsub(x,bmul([q[m]],y2))
		if(x2.length==0) {
		q[m]--
		x2=bsub(x,bmul([q[m]],y2))
		}
		x=x2
		}
		// de-normalize
		if(shift) {
		for(i=0; i<x.length-1; i++) x[i]=(x[i]>>shift) | ((x[i+1] << shift2) & bm); x[x.length-1]>>=shift
		}
		while(q.length > 1 && q[q.length-1]==0) q=q.slice(0,q.length-1)
		while(x.length > 1 && x[x.length-1]==0) x=x.slice(0,x.length-1)
		this.mod=x
		this.q=q
		return this
	}

	function bmod(p,m) { // binary modulo
		if(m.length==1) {
		if(p.length==1) return [p[0] % m[0]]
		if(m[0] < bdm) return [simplemod(p,m[0])]
		}

		var r=bdiv(p,m)
		return r.mod
	}
	
	function simplemod(i,m) {
		// returns the mod where m < 2^bd
		if(m>bdm)
		return bmod(i,[m])
		var c=0, v
		for(var n=i.length-1; n>=0; n--) {
		v=i[n]
		c=((v >> bd) + (c<<bd)) % m
		c=((v & bdm) + (c<<bd)) % m
		}
		return c
		}
		function bmodexp(xx,y,m) { // binary modular exponentiation
		var r=[1], n, an,a, x=xx.concat()
		var mu=[]
		n=m.length*2;  mu[n--]=1;  for(; n>=0; n--) mu[n]=0; mu=bdiv(mu,m).q

		for(n=0; n<y.length; n++) {
		for(a=1, an=0; an<bs; an++, a<<=1) {
		if(y[n] & a) r=bmod2(bmul(r,x),m,mu)
		x=bmod2(bmul(x,x),m,mu)
		}
		}
		return r
	}
	
	function bmod2(x,m,mu) { // Barrett's modular reduction from HAC, 14.42, CRC Press
		var xl=x.length - (m.length << 1)
		if(xl > 0) {
		return bmod2(x.slice(0,xl).concat(bmod2(x.slice(xl),m,mu)),m,mu)
		}
		var ml1=m.length+1, ml2=m.length-1,rr
		//var q1=x.slice(ml2)
		//var q2=bmul(q1,mu)
		var q3=bmul(x.slice(ml2),mu).slice(ml1)
		var r1=x.slice(0,ml1)
		var r2=bmul(q3,m).slice(0,ml1)
		var r=bsub(r1,r2)
		//var s=('x='+x+'\nm='+m+'\nmu='+mu+'\nq1='+q1+'\nq2='+q2+'\nq3='+q3+'\nr1='+r1+'\nr2='+r2+'\nr='+r); 
		if(r.length==0) {
		r1[ml1]=1
		r=bsub(r1,r2)
		}
		for(var n=0;;n++) {
		rr=bsub(r,m)
		if(rr.length==0) break
		r=rr
		if(n>=3) return bmod2(r,m,mu)
		}
		return r
	}

	function sub2(a,b) {
		var r=bsub(a,b)
		if(r.length==0) {
		this.a=bsub(b,a)
		this.sign=1
		} else {
		this.a=r
		this.sign=0
		}
		return this
	}
	
	function signedsub(a,b) {
		if(a.sign) {
		if(b.sign) {
		return sub2(b,a)
		} else {
		this.a=badd(a,b)
		this.sign=1
		}
		} else {
		if(b.sign) {
		this.a=badd(a,b)
		this.sign=0
		} else {
		return sub2(a,b)
		}
		}
		return this
	}

	function modinverse(x,n) { // returns x^-1 mod n
		// from  Bryan Olson <bryanolson@my-deja.com> 
		var y=n.concat(), t, r, bq, a=[1], b=[0], ts
		a.sign=0; b.sign=0
		while( y.length > 1 || y[0]) {
		t=y.concat()
		r=bdiv(x,y)
		y=r.mod
		q=r.q
		x=t
		t=b.concat(); ts=b.sign
		bq=bmul(b,q)
		bq.sign=b.sign
		r=signedsub(a,bq)
		b=r.a; b.sign=r.sign
		a=t; a.sign=ts
		}
		if(beq(x,[1])==0) return [0] // No inverse; GCD is x
		if(a.sign) {
		a=bsub(n,a)
		}
		return a
	}

	function crt_RSA(m, d, p, q) {
		// Compute m**d mod p*q for RSA private key operations. -- Bryan Olson via deja.com
		var xp = bmodexp(bmod(m,p), bmod(d,bsub(p,[1])), p)
		var xq = bmodexp(bmod(m,q), bmod(d,bsub(q,[1])), q)
		var t=bsub(xq,xp);
		if(t.length==0) {
		t=bsub(xp,xq)
		t = bmod(bmul(t, modinverse(p, q)), q);
		t=bsub(q,t)
		} else {
		t = bmod(bmul(t, modinverse(p, q)), q);
		} 
		return badd(bmul(t,p), xp)
	}

	// conversion functions:
	// text to binary and binary to text, text to base64 and base64 to text
	// OK, so this isn't exactly base64 -- fix it if you care

	function t2b(s) {
		var bits=s.length*8, bn=1, r=[0], rn=0, sn=0, sb=1;
		var c=s.charCodeAt(0)
		for(var n=0; n<bits; n++) {
		if(bn > bm) {bn=1; r[++rn]=0; }
		if(c & sb)  r[rn]|=bn;
		bn<<=1
		if((sb<<=1) > 255) {sb=1; c=s.charCodeAt(++sn); }
		}
		return r;
	}
	
	function b2t(b) {
		var bits=b.length*bs, bn=1, bc=0, r=[0], rb=1, rn=0
		for(var n=0; n<bits; n++) {
		if(b[bc] & bn) r[rn]|=rb;
		if((rb<<=1) > 255) {rb=1; r[++rn]=0; }
		if((bn<<=1) > bm) {bn=1; bc++; }
		}
		while(r[rn]==0) {rn--;}
		var rr=''
		for(var n=0; n<=rn; n++) rr+=String.fromCharCode(r[n]);
		return rr;
	}
	
	b64s='abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"'
	
	function textToBase64(t) {
		var r=''; var m=0; var a=0; var tl=t.length-1; var c
		for(n=0; n<=tl; n++) {
		c=t.charCodeAt(n)
		r+=b64s.charAt((c << m | a) & 63)
		a = c >> (6-m)
		m+=2
		if(m==6 || n==tl) {
		r+=b64s.charAt(a)
		if((n%45)==44) {r+="\n"}
		m=0
		a=0
		}
		}
		return r
	}
	
	function base64ToText(t) {
		var r=''; var m=0; var a=0; var c
		for(n=0; n<t.length; n++) {
		c=b64s.indexOf(t.charAt(n))
		if(c >= 0) {
		if(m) {
		r+=String.fromCharCode((c << (8-m))&255 | a)
		}
		a = c >> m
		m+=2
		if(m==8) { m=0 }
		}
		}
		return r
	}

	// RC4 stream encryption
	// adapted from www.cpan.org crypt::rc4 -- thanks!
	function rc4(key, text) {
		var i, x, y, t, x2, kl=key.length;
		s=[];

		for (i=0; i<256; i++) s[i]=i
		y=0
		for(j=0; j<2; j++) {
		for(x=0; x<256; x++) {
		y=(key.charCodeAt(x%kl) + s[x] + y) % 256
		t=s[x]; s[x]=s[y]; s[y]=t
		}
		}
		var z=""
		for (x=0; x<text.length; x++) {
		x2=x & 255
		y=( s[x2] + y) & 255
		t=s[x2]; s[x2]=s[y]; s[y]=t
		z+= String.fromCharCode((text.charCodeAt(x) ^ s[(s[x2] + s[y]) % 256]))
		}
		return z
	}

	function ror(a,n) {n&=7; return n?((a>>n) | ((a<<(8-n))&255)):a;}
	
	function hash(s,l) {
		var sl=s.length,r=[],rr='',v=1,lr=4;
		for(var n=0; n<l; n++) r[n]=(v=((v*v*5081+n) & 255));
		while(sl--) {
		lr = r[sl % l] ^= ror(s.charCodeAt(sl),lr) ^ r[r[(sl * 5081) % l] % l];
		}
		for(var n=0; n<l; n++)
		rr+=String.fromCharCode(r[n] ^
		ror(r[r[(n * 171) % l] % l],r[n]));
		return rr
	}

	// tie it all together with rsa encrypt and decrypt
	rsaEncode = function(key,mod,text) {
		// create a good random session key
		var keylen=Math.floor((mod.length+1)*bs/8)
		var sessionkey=hash(text+Date()+Math.random(),keylen)

		// sessionkey must be less than modulo
		sessionkey=bmod(t2b(sessionkey),mod)

		// convert it from arbitrary precision representation into text for RC4
		var sk2=b2t(sessionkey)

		// rsa encrypt the key
		var ske=bmodexp(sessionkey,key,mod)

		// to pack it in with the text we need its length
		var skeText=b2t(ske)

		// return the rsa encoded key and the encrypted text
		// pack up the completed encoded package with base64
		return escape(textToBase64(
		String.fromCharCode(skeText.length)+skeText+
		rc4(sk2,text)))
	};

	rsaDecode = function(key,text) {
		text = unescape(text);

		// separate the session key from the text
		text=base64ToText(text)
		var sessionKeyLength=text.charCodeAt(0)
		var sessionKeyEncryptedText=text.substr(1,sessionKeyLength)
		text=text.substr(sessionKeyLength+1)
		var sessionKeyEncrypted=t2b(sessionKeyEncryptedText)

		// un-rsa the session key
		sessionkey=crt_RSA(sessionKeyEncrypted,key[0],key[1],key[2])
		sessionkey=b2t(sessionkey)

		text=rc4(sessionkey,text)
		return text
	};
	
    mytables = (function () {
    	var 
    		// Domain...
    		_domainPath = '',
    		
    		// app name...
    		_appName = '',
    		
    		// s3 details
    		_s3aKy = '',
    		_s3stKy = '',
    		_s3rg = '',
    		
    		// status of last executed function
    		_status = '-1',
    		_statusMsg = '',
    		
    		// name of function last executed
    		//_lastExec = '',
    		
    		_init = function (domain, app, aKy, stKy, rg) {
    			if (domain === undefined || domain === '' || domain.indexOf(' ') >= 0) {
    				console.log('_init = domain name cannot contain spaces or be undefined or be an empty string');
    				return;
    			}

    			if (app === undefined || app === '' || app.indexOf(' ') >= 0) {
    				console.log('_init = app name cannot contain spaces or be undefined or be an empty string');
    				return;
    			}

    			_domainPath = domain + '/tables';
    			_appName = 'bel_' + app;
    			
    			_s3aKy = rsaEncode([17], [148299941,57683965,5687041], aKy);
    			_s3stKy = rsaEncode([17], [148299941,57683965,5687041], stKy);
    			_s3rg = rg;
    		},

    		_utils = {

	    		encrypt : function (str) {
	    			return rsaEncode([17], [148299941,57683965,5687041], str);
	    		},

	    		decrypt : function (str) {
	    			return rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], str);
	    		},

	    		createUUID : function() {
	    			function _p8(s) {
        				var p = (Math.random().toString(16)+"000000000").substr(2,8);
        				return s ? "-" + p.substr(0,4) + "-" + p.substr(4,4) : p ;
    				}
    				return _p8() + _p8(true) + _p8(true) + _p8();
				}

    		},
    		
    		_db = {
    		
    			parseJsonResult : function (result) {
					var jsonStr = JSON.stringify(result);
  					return JSON.parse(eval('(' + jsonStr + ')'));
				},
				
				isObject : function (a) {
    				return (!!a) && (a.constructor === Object);
				},
				
				hasOwnValue : function (obj, pp, val) {
    				for (var prop in obj) {
    				
        				if (obj.hasOwnProperty(prop) && obj[prop] === val &&
        					prop.toString().toLowerCase().indexOf(pp.toString().toLowerCase()) >= 0) {
            				return true;   
        				}
    				}
    				
    				return false;
				},
				
				hasOwnValueStr : function (obj, pp, val) {
    				for (var prop in obj) {
    					var p = obj[prop];
    					
    					if (obj.hasOwnProperty(prop) && 
        					prop.toString().toLowerCase().indexOf(pp.toString().toLowerCase()) >= 0 &&
        					p.toString().toLowerCase().indexOf(val.toString().toLowerCase()) >= 0) {
            				return true;   
        				}
    				}
    				
    				return false;
				},
				
				updatePropValue : function (obj, pp, newVal) {
					var newObj = obj;
					
					for (var prop in obj) {
						var p = obj[prop];
						
						if (obj.hasOwnProperty(prop) && 
        					prop.toString().toLowerCase().indexOf(pp.toString().toLowerCase()) >= 0) {
            				
            				newObj[prop] = newVal;
            				return newObj;
        				}
					}
					
					return newObj;
				},
    		
    			itemExists : function (table, itemName, item, sParams, fParams, onFound, onNotFound) {
    			
    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'itemExists = empty domainPath or appName');
    					return;
    				}

    				if (table === undefined || table === '' || item === undefined || item === '' || itemName === undefined || itemName === '') {
    					onNotFound(fParams, 'itemExists = empty table, itemName or item');
    					return;
    				}

    				if (table.indexOf(' ') >= 0 || itemName.indexOf(' ') >= 0 || item.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemExists = table, itemName, item cannot contain spaces');
    					return;
    				}
    				
    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null && data !== undefined) {
   								if (data.length > 0) {
   									var found = false;

   									for (var i = 0; i <= data.length - 1; i++) {
   										var obj = _db.parseJsonResult(rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i]));

   										if (_db.hasOwnValueStr(obj, itemName, item)) {
   											onFound(obj, sParams, 'itemExists = found');
   											found = true;
   										}
   									}

   									if (!found) {
   										onNotFound(fParams, 'itemExists = no elements in returned result');
   									}
   								}
   								else {
   									onNotFound(fParams, 'itemExists = no elements in returned result');
   								}
   							}
   							else {
   								onNotFound(fParams, 'itemExists = null or undefined return value');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemExists = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
 					});
    			},
    			
    			itemCore : function (fName, apiName, table, itemName, item, sParams, fParams, onFound, onNotFound) {

    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, fName + ' = empty domainPath or appName');
    					return;
    				}

    				if (table === undefined || table === '' || item === undefined || item === '' || itemName === undefined || itemName === '') {
    					onNotFound(fParams, fName + ' = empty table, itemName or item');
    					return;
    				}

    				if (table.indexOf(' ') >= 0 || itemName.indexOf(' ') >= 0 || item.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemCore = table, itemName, item cannot contain spaces');
    					return;
    				}
    				
    				//_lastExec = fName;
    				
    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null && data !== undefined) {
   								if (data.length > 0) {
   									var found = false;

   									for (var i = 0; i <= data.length - 1; i++) {
   										var di = rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i]),
   											obj = _db.parseJsonResult(di);
   										
   										if (_db.hasOwnValueStr(obj, itemName, item)) {
   											$.ajax({
   												type: 'GET',
   												url: _domainPath + '/' + apiName + '/' + _appName + '_' + table + '/' + di
   													 + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   												success: function (result) {
   													onFound(result, sParams, fName + ' = deleted');
   													found = true;
   												},
   												error: function (XMLHttpRequest, textStatus, errorThrown) {
													onNotFound(fParams, fName + ' = failed: ' + textStatus + ' -> ' + errorThrown);
   												}
   											});
   										}
   									}

   									if (!found) {
   										onNotFound(fParams, fName + ' = no elements in returned result');
   									}
   								}
   								else {
   									onNotFound(fParams, fName + ' = no elements in returned result');
   								}
   							}
   							else {
   								onNotFound(fParams, fName + ' = null or undefined return value');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, fName + ' = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},
    			
    			itemDelete : function (table, itemName, item, sParams, fParams, onFound, onNotFound) {
    				_db.itemCore('itemDelete', 'deleterow', table, itemName, item, sParams, fParams, onFound, onNotFound);
    			},

    			itemQueryOr : function (table, searchName, whereName, whereValues, results, sParams, fParams, onFound, onNotFound, strict, asObject) {
    				results = [];

    				if (table === undefined || table === '') {
    					onNotFound(fParams, 'itemQueryOr = empty table');
    					return;
    				}

    				if (table.indexOf(' ') >= 0 || whereName.indexOf(' ') >= 0 || whereValues.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemQueryOr = table, whereName, whereValues cannot contain spaces');
    					return;
    				}

    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'itemQueryOr = empty domainPath or appName');
    					return;
    				}

    				if (whereValues === undefined || whereValues === '' || whereName === undefined || whereName === '') {
    					onNotFound(fParams, 'itemQueryOr = empty whereName or whereValues');
    					return;	
    				}

    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null || data !== undefined) {
   								if (data.length > 0) {
   									for (var i = 0; i <= data.length - 1; i++) {
   										var dd = rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i]),
   											obj = _db.parseJsonResult(dd),
   											okSearchName = true;

   										if (searchName !== undefined) {
   											okSearchName = (obj.hasOwnProperty(searchName)) ? true : false;
   										}

   										var wValues = [];

   										if (whereValues.indexOf('|') >= 0) {
   											wValues = whereValues.split('|');
   										}
   										else {
   											wValues.push(whereValues);
   										}
   										
   										if (wValues !== undefined && wValues.length > 0) {
   											for (var j = 0; j <= wValues.length - 1; j++) {
   												var wVal = wValues[j];

   												if (strict) {
   													if (okSearchName && _db.hasOwnValue(obj, whereName, wVal)) {
   														if (asObject) {
   															results.push(obj);
   														}
   														else {
   															results.push(dd);
   														}
   													}
   												}
   												else {
   													if (okSearchName && _db.hasOwnValueStr(obj, whereName, wVal)) {
   														if (asObject) {
   															results.push(obj);
   														}
   														else {
   															results.push(dd);
   														}
   													}
   												}
   											}
   										}
   									}

   									if (results.length > 0) {
   										onFound(results, sParams, 'itemQueryOr = found items');
   									}
   									else {
   										onNotFound(fParams, 'itemQueryOr = items not found');
   									}
   								}
   								else {
   									onNotFound(fParams, 'itemQueryOr = items not found');
   								}
   							}
   							else {
   								onNotFound(fParams, 'itemQueryOr = items not found');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemQueryOr = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},

    			listAll : function (table, results, sParams, fParams, onFound, onNotFound, asObject) {
    				results = [];

    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'listAll = empty domainPath or appName');
    					return;
    				}

    				if (table === undefined || table === '') {
    					onNotFound(fParams, 'listAll = empty table');
    					return;
    				}

    				if (table.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'listAll = table cannot contain spaces');
    					return;
    				}

    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null || data !== undefined) {
   								if (data.length > 0) {
   									for (var i = 0; i <= data.length - 1; i++) {
   										var dd = rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i]),
   											obj = _db.parseJsonResult(dd);

   										if (asObject) {
   											results.push(obj);
   										}
   										else {
   											results.push(dd);
   										}
   									}

   									if (results.length > 0) {
   										onFound(results, sParams, 'listAll = found items');
   									}
   									else {
   										onNotFound(fParams, 'listAll = items not found');
   									}
   								}
   								else {
   									onNotFound(fParams, 'listAll = items not found');
   								}
   							}
   							else {
   								onNotFound(fParams, 'listAll = items not found');	
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'listAll = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},

    			itemQueryAnd : function (table, searchName, whereName0, whereValue0, whereName1, whereValue1, results, sParams, fParams, onFound, onNotFound, strict, asObject) {
    				results = [];

    				if (table === undefined || table === '') {
    					onNotFound(fParams, 'itemQueryAnd = empty table');
    					return;
    				}

    				if (table.indexOf(' ') >= 0 || whereName0.indexOf(' ') >= 0 || whereValue0.indexOf(' ') >= 0 ||
    					whereName1.indexOf(' ') >= 0 || whereValue1.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemQueryAnd = table, whereNameX, whereValuesX cannot contain spaces');
    					return;
    				}

    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'itemQueryAnd = empty domainPath or appName');
    					return;
    				}

    				if (whereValue0 === undefined || whereValue0 === '' || whereName0 === undefined || whereName0 === '' &&
    					whereValue1 === undefined || whereValue1 === '' || whereName1 === undefined || whereName1 === '') {
    					onNotFound(fParams, 'itemQueryAnd = empty whereNamesX or whereValuesX');
    					return;	
    				}

    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null || data !== undefined) {
   								if (data.length > 0) {
   									for (var i = 0; i <= data.length - 1; i++) {
   										var dd = rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i]),
   											obj = _db.parseJsonResult(dd),
   											okSearchName = true;
   										
   										if (searchName !== undefined) {
   											okSearchName = (obj.hasOwnProperty(searchName)) ? true : false;
   										}
   										
   										if (strict) {
   											if (okSearchName && _db.hasOwnValue(obj, whereName0, whereValue0) &&
   												_db.hasOwnValue(obj, whereName1, whereValue1)) {
   												if (asObject) {
   													results.push(obj);
   												}
   												else {
   													results.push(dd);
   												}
   											}
   										}
   										else {
   											if (okSearchName && _db.hasOwnValueStr(obj, whereName0, whereValue0) &&
   												_db.hasOwnValueStr(obj, whereName1, whereValue1)) {
   												if (asObject) {
   													results.push(obj);
   												}
   												else {
   													results.push(dd);
   												}
   											}
   										}
   									}

   									if (results.length > 0) {
   										onFound(results, sParams, 'itemQueryAnd = found items');
   									}
   									else {
   										onNotFound(fParams, 'itemQueryAnd = items not found');
   									}
   								}
   								else {
   									onNotFound(fParams, 'itemQueryAnd = items not found');
   								}
   							}
   							else {
   								onNotFound(fParams, 'itemQueryAnd = items not found');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemQueryAnd = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},
    			
    			itemQuery : function (table, searchName, whereName, whereValue, results, sParams, fParams, onFound, onNotFound, strict, asObject) {
    				results = [];

    				if (table.indexOf(' ') >= 0 || whereName.indexOf(' ') >= 0 || whereValue.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemQuery = table, whereName, whereValue cannot contain spaces');
    					return;
    				}
    				
    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'itemQuery = empty domainPath or appName');
    					return;
    				}

    				if (whereValue === undefined || whereValue === '' || whereName === undefined || whereName === '') {
    					onNotFound(fParams, 'itemQuery = empty whereName or whereValue');
    					return;	
    				}

    				if (table === undefined || table === '') {
    					onNotFound(fParams, 'itemQuery = empty table');
    					return;
    				}
    				
    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null || data !== undefined) {
   								if (data.length > 0) {
   									for (var i = 0; i <= data.length - 1; i++) {
   										var dd = rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i]),
   											obj = _db.parseJsonResult(dd),
   											okSearchName = true;
   										
   										if (searchName !== undefined) {
   											okSearchName = (obj.hasOwnProperty(searchName)) ? true : false;
   										}
   										
   										if (strict) {
   											if (okSearchName && _db.hasOwnValue(obj, whereName, whereValue)) {
   												if (asObject) {
   													results.push(obj);
   												}
   												else {
   													results.push(dd);
   												}
   											}
   										}
   										else {
   											if (okSearchName && _db.hasOwnValueStr(obj, whereName, whereValue)) {
   												if (asObject) {
   													results.push(obj);
   												}
   												else {
   													results.push(dd);
   												}
   											}
   										}
   									}
   									
   									if (results.length > 0) {
   										onFound(results, sParams, 'itemQuery = found items');
   									}
   									else {
   										onNotFound(fParams, 'itemQuery = items not found');
   									}
   								}
   								else {
   									onNotFound(fParams, 'itemQuery = items not found');
   								}
   							}
   							else {
   								onNotFound(fParams, 'itemQuery = items not found');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemQuery = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},

    			itemUpdateValidation : function (table, whereName, whereValue, fieldName, fieldNewValue) {
    				if (table === undefined || table === '') {
    					onNotFound(fParams, 'itemUpdate = empty table');
    					return;
    				}

    				if (table.indexOf(' ') >= 0 || whereName.indexOf(' ') >= 0 || whereValue.indexOf(' ') >= 0 ||
    					fieldName.indexOf(' ') >= 0 || fieldNewValue.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemUpdateValidation = table, whereName, whereValue, fieldName, fieldNewValue cannot contain spaces');
    					return;
    				}

    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'itemUpdateValidation = empty domainPath or appName');
    					return;
    				}

    				if (whereValue === undefined || whereValue === '' || whereName === undefined || whereName === '') {
    					onNotFound(fParams, 'itemUpdateValidation = empty whereName or whereValue');
    					return;	
    				}

    				if (fieldName === undefined || fieldName === '' || fieldNewValue === undefined || fieldNewValue === '') {
    					onNotFound(fParams, 'itemUpdateValidation = empty fieldName or fieldNewValue');
    					return;
    				}
    			},

    			itemUpdateCoreAnd : function (table, whereName0, whereValue0, whereName1, whereValue1, fieldName, fieldNewValue, sParams, fParams, onFound, onNotFound) {
    				var nFnd = 0;

    				$.ajax({
    					type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
    					success: function (data) {
    						if (data !== null || data !== undefined) {
   								if (data.length > 0) {
   									for (var i = 0; i <= data.length - 1; i++) {
   										var obj = _db.parseJsonResult(rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i])),
   											objData = JSON.parse(JSON.stringify(obj));

   										var newObj = null;

   										if (obj.hasOwnProperty(fieldName) && 
	   										_db.hasOwnValueStr(obj, whereName0, whereValue0) &&
	   										_db.hasOwnValueStr(obj, whereName1, whereValue1)) {

    										var tempObj = _db.updatePropValue(obj, fieldName, fieldNewValue);
    												
    										var newObject = JSON.stringify(tempObj);
											newObj = JSON.parse(newObject);
    									}

    									if (newObj !== null) {
    										$.ajax({
	   											type: 'GET',
	   											url: _domainPath + '/updaterow/' + _appName + '_' + table + '/' + JSON.stringify(objData) + '/' + JSON.stringify(newObj)
	   												+ '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
	   											success: function (result) {
	   												onFound(result, sParams, 'itemUpdateCoreAnd = updated');
	   												nFnd++;
	   											},
	   											error: function (XMLHttpRequest, textStatus, errorThrown) {
													onNotFound(fParams, 'itemUpdateCoreAnd = failed: ' + textStatus + ' -> ' + errorThrown);
	   											}
	   										});
    									}
   									}

   									if (nFnd === 0) {
   										onNotFound(fParams, 'itemUpdateCoreAnd = items not found');
   									}
   								}
   								else {
   									onNotFound(fParams, 'itemUpdateCoreAnd = items not found');
   								}
   							}
   							else {
   								onNotFound(fParams, 'itemUpdateCoreAnd = items not found');
   							}
    					},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemUpdateCoreAnd = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},

    			itemUpdateCore : function (table, whereName, whereValue, fieldName, fieldNewValue, sParams, fParams, onFound, onNotFound) {
    				var nFnd = 0;

    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null || data !== undefined) {
   								if (data.length > 0) {
   									for (var i = 0; i <= data.length - 1; i++) {
   										var obj = _db.parseJsonResult(rsaDecode([[119141457,185046352,2676254],[40632295,2191],[122927507,2595]], data[i])),
   											objData = JSON.parse(JSON.stringify(obj));

   										var iFieldName = [], iWhereName = [], iWhereValue = [], iFieldNewValue = [];

   										if (fieldName.indexOf('|') >= 0) {
    										iFieldName = fieldName.split('|');
    									}
    									else {
    										iFieldName.push(fieldName);
    									}

    									if (whereName.indexOf('|') >= 0) {
    										iWhereName = whereName.split('|');
    									}
    									else {
    										iWhereName.push(whereName);
    									}

    									if (whereValue.indexOf('|') >= 0) {
    										iWhereValue = whereValue.split('|');
    									}
    									else {
    										iWhereValue.push(whereValue);
    									}

    									if (fieldNewValue.indexOf('|') >= 0) {
    										iFieldNewValue = fieldNewValue.split('|');
    									}
    									else {
    										iFieldNewValue.push(fieldNewValue);
    									}

    									if (iFieldName.length > 0 && iWhereName.length > 0 && 
    										iWhereValue.length > 0 && iFieldNewValue.length > 0 &&
    										iFieldName.length === iWhereName.length && 
    										iWhereValue.length === iFieldNewValue.length) {

    										var newObj = null;

    										for (var j = 0; j <= iFieldName.length - 1; j++) {
    											if (newObj !== null) {
    												obj = newObj;
    											}

    											if (obj.hasOwnProperty(iFieldName[j]) && 
	   												_db.hasOwnValueStr(obj, iWhereName[j], iWhereValue[j])) {

    												var tempObj = _db.updatePropValue(obj, iFieldName[j], iFieldNewValue[j]);
    												
    												var newObject = JSON.stringify(tempObj);
													newObj = JSON.parse(newObject);
    											}
    										}

    										if (newObj !== null) {
    											$.ajax({
	   												type: 'GET',
	   												url: _domainPath + '/updaterow/' + _appName + '_' + table + '/' + JSON.stringify(objData) + '/' + JSON.stringify(newObj)
	   													+ '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
	   												success: function (result) {
	   													onFound(result, sParams, 'itemUpdateCore = updated');
	   													nFnd++;
	   												},
	   												error: function (XMLHttpRequest, textStatus, errorThrown) {
														onNotFound(fParams, 'itemUpdateCore = failed: ' + textStatus + ' -> ' + errorThrown);
	   												}
	   											});
    										}
    									}
   									}
   									
   									if (nFnd === 0) {
   										onNotFound(fParams, 'itemUpdateCore = items not found');
   									}
   								}
   								else {
   									onNotFound(fParams, 'itemUpdateCore = items not found');
   								}
   							}
   							else {
   								onNotFound(fParams, 'itemUpdateCore = items not found');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemUpdateCore = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			},

    			itemUpdate : function (table, whereName, whereValue, fieldName, fieldNewValue, sParams, fParams, onFound, onNotFound) {
    				var nFnd = 0;

    				_db.itemUpdateValidation(table, whereName, whereValue, fieldName, fieldNewValue);
    				_db.itemUpdateCore(table, whereName, whereValue, fieldName, fieldNewValue, sParams, fParams, onFound, onNotFound);
    			},

    			itemUpdateAnd : function (table, whereName0, whereValue0, whereName1, whereValue1, fieldName, fieldNewValue, sParams, fParams, onFound, onNotFound) {
    				var nFnd = 0;

    				_db.itemUpdateValidation(table, whereName0, whereValue0, fieldName, fieldNewValue);
    				_db.itemUpdateCoreAnd(table, whereName0, whereValue0, whereName1, whereValue1, fieldName, fieldNewValue, sParams, fParams, onFound, onNotFound);
    			},
    			
    			itemCreate : function (table, objData, sParams, fParams, onFound, onNotFound) {
    				
    				if (table.indexOf(' ') >= 0) {
    					onNotFound(fParams, 'itemCreate = table name cannot contain spaces');
    					return;
    				}

    				if (_domainPath === undefined || _appName === undefined || _domainPath === '' || _appName === '') {
    					onNotFound(fParams, 'itemCreate = empty domainPath or appName');
    					return;
    				}
    				
    				$.ajax({
   						type: 'GET',
   						url: _domainPath + '/listrows/' + _appName + '_' + table + '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   						success: function (data) {
   							if (data !== null || data !== undefined) {
   								$.ajax({
   									type: 'GET',
   									url: _domainPath + '/insertrow/' + _appName + '_' + table + '/' + JSON.stringify(objData)
   										+ '/' + _s3aKy + '/' + _s3stKy + '/' + _s3rg,
   									success: function (result) {
   										onFound(result, sParams, 'itemCreate = created');
   										return;
   									},
   									error: function (XMLHttpRequest, textStatus, errorThrown) {
										onNotFound(fParams, 'itemCreate = failed: ' + textStatus + ' -> ' + errorThrown);
   									}
   								});
   							}
   							else {
   								onNotFound(fParams, 'itemCreate = null or undefined return value');
   							}
   						},
   						error: function (XMLHttpRequest, textStatus, errorThrown) {
							onNotFound(fParams, 'itemCreate = failed: ' + textStatus + ' -> ' + errorThrown);
   						}
   					});
    			}
    		},
    		
    		_about = function (showdmn) {
    			console.log('MyTabl.es - http://mytabl.es/');
    			console.log('FastDoks, inc - 2014 - All rights reserved');
    			
    			if (showdmn) {
    				console.log('domain: ' + _domainPath + ' / app: ' + _appName);
    			}
    		};
	    
	    return {
    		about: _about,
    		init: _init,
    		db: _db,
    		utils: _utils,
    		status: _status,
    		statusMsg: _statusMsg
    	}
    	
	})();
	
})(window.jQuery);