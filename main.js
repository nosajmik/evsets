function mean(arr) {
	return arr.reduce((a,b) => a+b) / arr.length;
}

function median(arr) {
	arr.sort((a,b) => a-b);
	return (arr.length % 2) ? arr[(arr.length / 2) | 0] : mean([arr[arr.length/2 - 1], arr[arr.length / 2]]);
}

// Overload
Function.prototype.toSource = function() {
return this.toString().slice(this.toString().indexOf('{')+1,-1);
}

Object.defineProperty(Array.prototype, 'chunk', {
value: function(n){
	let results = [];
	let ceiled = this.length%n;
	let k = Math.ceil(this.length/n);
	let q = Math.floor(this.length/n);
	let c = 0;
	for (i=0; i<ceiled; i++) {
		results[i] = this.slice(c, c+k);
		c += k;
	}
	for (i; i<n; i++) {
		results[i] = this.slice(c, c+q);
		c += q;
	}
	return results;
}
});

function EvSet(view, nblocks, start=8192, victim=4096, assoc=16, stride=4096, offset=0) {

	const RAND = true;

	/* private methods */
	this.genIndices = function (view, stride) {
		let arr = [], j = 0;
		for (let i=(stride)/4; i < (view.byteLength-this.start)/4; i += stride/4) {
			arr[j++] = this.start + this.offset + i*4;
		}
		arr.unshift(this.start + this.offset);
		return arr;
	}

	this.randomize = function (arr) {
		for (let i = arr.length; i; i--) {
			var j = Math.floor(Math.random() * i | 0) | 0;
			[arr[i - 1], arr[j]] = [arr[j], arr[i - 1]];
		}
		return arr;
	}

	this.indicesToLinkedList =  function (buf, indices) {
		if (indices.length == 0) {
			this.ptr = 0;
			return;
		}
		let pre = this.ptr = indices[0];
		for (let i=1; i<indices.length; i++) {
			view.setUint32(pre, indices[i], true);
			pre = indices[i];
		}
		view.setUint32(pre, 0, true);
	}

	this.init = function() {
		let indx = this.genIndices(view, stride);
		if (RAND) indx = this.randomize(indx);
		indx.splice(nblocks, indx.length); // select nblocks elements
		this.indicesToLinkedList(view, indx);
		return indx;
	}
	/* end-of-private */

	/* properties */
	this.start = start;
	this.offset = (offset&0x3f)<<6;
	this.victim = victim+this.offset;
	view.setUint32(this.victim, 0, true); // lazy alloc
	this.assoc = assoc;
	this.ptr = 0;
	this.refs = this.init();
	this.del = [];
	/* end-of-properties */

	/* public methods */
	this.unlinkChunk = function unlinkChunk(chunk) {
		let s = this.refs.indexOf(chunk[0]), f = this.refs.indexOf(chunk[chunk.length-1]);
		view.setUint32(this.refs[f], 0, true);
		this.refs.splice(s, chunk.length); // splice chunk indexes
		if (this.refs.length === 0) { // empty list
			this.ptr = 0;
		} else if (s === 0) { // removing first chunk
			this.ptr = this.refs[0];
		} else if (s > this.refs.length-1) { // removing last chunk
			view.setUint32(this.refs[this.refs.length-1], 0, true);
		} else { // removing middle chunk
			view.setUint32(this.refs[s-1], this.refs[s], true);
		}
		this.del.push(chunk); // right
	}

	this.relinkChunk = function relinkChunk() {
		let chunk = this.del.pop(); // right
		if (chunk === undefined) {
			return;
		}
		this.ptr = chunk[0];
		if (this.refs.length > 0) {
			view.setUint32(chunk[chunk.length-1], this.refs[0], true);
		}
		if (typeof(chunk) === 'number') {
			this.refs.unshift(chunk); // left
		} else {
			this.refs.unshift(...chunk); // left
		}
	}

	this.groupReduction = function groupReduction(callback, threshold) {
		const MAX = 500;
		let r = 0;
		while (this.refs.length > this.assoc) {
			let m = this.refs.chunk(16+1); // may need to change this to this.assoc + 1 for M1
			let found = false;
			for (let c in m) {
				this.unlinkChunk(m[c]);
				let t = median(callback(this.victim, this.ptr));
				// console.log(t);
				if (t < threshold) {
					this.relinkChunk();
				} else {
					found = true;
					break;
				}
			}
			if (!found) {
				r += 1;
				if (r < MAX) {
					this.relinkChunk();
					if (this.del.length === 0) break;
				} else {
					while (this.del.length > 0) {
						this.relinkChunk();
					}
					break;
				}
			};	
		}
	}

	this.relink = function () {
		this.indicesToLinkedList(this.buffer, this.refs);
	}
}

// Constants
const PAGE_SZ = 4096;
const THRESHOLD = 0.0001;

async function run() {
	const BM = 128*1024*1024; // Eviction buffer
	const WP = 64*1024; // A WebAssembly page has a constant size of 64KB
	const SZ = BM/WP; // 128 hardcoded value in wasm

	// Shared memory
	const memory = new WebAssembly.Memory({initial: SZ, maximum: SZ})

	const B = PAGE_SZ * 2;
	const OFFSET = 0;
	const ASSOC = 64;
	const STRIDE = PAGE_SZ;

	// Memory view
	const view = new DataView(memory.buffer);

	console.log('Prepare new evset');
	const evset = new EvSet(view, B, PAGE_SZ*2, PAGE_SZ, ASSOC, STRIDE, OFFSET);

	const RETRY = 10;
	await new Promise(r => setTimeout(r, 10)); // timeout to allow counter

	let r = 0;
	while (!cb(evset, view) && ++r < RETRY && evset.victim) {
		console.log('retry');
		first = false;
	}

	console.log('EOF');
}

function cb(evset, view) {

    const REP = 6;
	
	function miss(vic, ptr) {
		let t, total = [];
		for (let i=0; i<REP; i++) {
			let crap = 0;
			crap = view.getUint32(vic, true); // initial victim access
			let head = ptr + crap - crap;
			// Prevent out of order execution! + crap - crap is there
			// to introduce a data dependency between the initial victim access
			// and the candidate set traversal. Luckily Safari's optimizer is
			// not so smart into looking at program semantics and doesn't get rid
			// of the + crap - crap.
			while (head != 0) head = view.getUint32(head, true);
			let junk = 0;
			const t1 = performance.now();
			junk = view.getUint32(vic, true); // victim reaccess
			const t2 = performance.now();
			t = t2 - t1 + junk - junk;
			// Creating data dependency for the reaccess so it won't get
			// optimized out. 
			// t = wasm_miss(vic, ptr);
			total.push(Number(t));
		}
		return total;
	}

	console.log('Starting reduction...');
	evset.groupReduction(miss, THRESHOLD);
	
	if (evset.refs.length <= evset.assoc) {
		console.log('Victim addr: ' + evset.victim);
		console.log('Eviction set: ' + evset.refs);
		console.log("Timings with eviction set traversal");
		for (let i=0; i<10; i++) {
			console.log(median(miss(evset.victim, evset.ptr)));
		}
		console.log("Timings without eviction set traversal");
		for (let i=0; i<10; i++) {
			console.log(median(miss(evset.victim, 0)));
		}
		evset.del = evset.del.flat();
		return true;
	} else {
		while (evset.del.length > 0) {
			evset.relinkChunk();
		}
		console.log('Failed: ' + evset.refs.length);
		return false;
	}
}
