
// ============================================
// NETWORK UTILITY - CLOUDFLARE WORKER
// ============================================

import { connect } from "cloudflare:sockets";

// ==================== KONSTANTA ====================
const internalKey = "3b01a777-55e7-49f6-8637-d94ee69607c6";
const DNS_PORT = 53;

const TYPES = {
    TYPE_A: 'a',
    TYPE_B: 'b',
    TYPE_C: 'c',
    TYPE_D: 'd'
};

const DETECTION_PATTERNS = {
    DELIMITER_P1: [0x0d, 0x0a],
    DELIMITER_P1_CHECK: [0x01, 0x03, 0x7f],
    UUID_V4_REGEX: /^w{8}w{4}4w{3}[89ab]w{3}w{12}$/,
    BUFFER_MIN_SIZE: 62,
    DELIMITER_OFFSET: 56
};

const ADDRESS_TYPES = {
    IPV4: 1,
    DOMAIN: 2,
    DOMAIN_ALT: 3,
    IPV6: 4
};

const COMMAND_TYPES = {
    TCP: 1,
    UDP: 2,
    UDP_ALT: 3
};

// Internal crypto constants
const CRYPTO_SALT_1 = new TextEncoder().encode("Header AEAD Key_Length");
const CRYPTO_SALT_2 = new TextEncoder().encode("Header AEAD Nonce_Length");
const CRYPTO_SALT_3 = new TextEncoder().encode("Header AEAD Key");
const CRYPTO_SALT_4 = new TextEncoder().encode("Header AEAD Nonce");
const CRYPTO_SALT_5 = new TextEncoder().encode("Resp Header Len Key");
const CRYPTO_SALT_6 = new TextEncoder().encode("Resp Header Len IV");
const CRYPTO_SALT_7 = new TextEncoder().encode("Resp Header Key");
const CRYPTO_SALT_8 = new TextEncoder().encode("Resp Header IV");

const WS_READY_STATE_OPEN = 1;
const WS_READY_STATE_CLOSING = 2;

let routeConfig = "";

// ==================== HELPER FUNCTIONS ====================
const toBytes = (str) => new TextEncoder().encode(str);
const fromBytes = (arr) => new TextDecoder().decode(arr);
const mergeBytes = (...arrays) => {
    const result = new Uint8Array(arrays.reduce((sum, arr) => sum + arr.length, 0));
    let offset = 0;
    for (const arr of arrays) {
        result.set(arr, offset);
        offset += arr.length;
    }
    return result;
};
const createBuffer = (size, fill = 0) => {
    const arr = new Uint8Array(size);
    if (fill) arr.fill(fill);
    return arr;
};

function base64ToBuffer(base64Str) {
    if (!base64Str) return { error: null };
    try {
        base64Str = base64Str.replace(/-/g, "+").replace(/_/g, "/");
        const decode = atob(base64Str);
        const arryBuffer = Uint8Array.from(decode, (c) => c.charCodeAt(0));
        return { earlyData: arryBuffer.buffer, error: null };
    } catch (error) {
        return { error };
    }
}

function bufferToHex(buffer) {
    return [...new Uint8Array(buffer)].map((x) => x.toString(16).padStart(2, "0")).join("");
}

// ==================== CRYPTO FUNCTIONS ====================
function hashSHA256(message) {
    const msg = message instanceof Uint8Array ? message : toBytes(message);
    const K = new Uint32Array([
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ]);
    let H = new Uint32Array([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]);
    const rotr = (x, n) => (x >>> n) | (x << (32 - n));
    const len = msg.length;
    const paddingLen = ((56 - (len + 1) % 64) + 64) % 64;
    const padded = new Uint8Array(len + 1 + paddingLen + 8);
    padded.set(msg);
    padded[len] = 0x80;
    new DataView(padded.buffer).setUint32(padded.length - 4, len * 8, false);
    const W = new Uint32Array(64);
    for (let i = 0; i < padded.length; i += 64) {
        const block = new DataView(padded.buffer, i, 64);
        for (let t = 0; t < 16; t++) W[t] = block.getUint32(t * 4, false);
        for (let t = 16; t < 64; t++) {
            const s0 = rotr(W[t - 15], 7) ^ rotr(W[t - 15], 18) ^ (W[t - 15] >>> 3);
            const s1 = rotr(W[t - 2], 17) ^ rotr(W[t - 2], 19) ^ (W[t - 2] >>> 10);
            W[t] = (W[t - 16] + s0 + W[t - 7] + s1) >>> 0;
        }
        let [a, b, c, d, e, f, g, h] = H;
        for (let t = 0; t < 64; t++) {
            const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
            const ch = (e & f) ^ (~e & g);
            const T1 = (h + S1 + ch + K[t] + W[t]) >>> 0;
            const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
            const maj = (a & b) ^ (a & c) ^ (b & c);
            const T2 = (S0 + maj) >>> 0;
            h = g; g = f; f = e; e = (d + T1) >>> 0;
            d = c; c = b; b = a; a = (T1 + T2) >>> 0;
        }
        H[0] = (H[0] + a) >>> 0; H[1] = (H[1] + b) >>> 0;
        H[2] = (H[2] + c) >>> 0; H[3] = (H[3] + d) >>> 0;
        H[4] = (H[4] + e) >>> 0; H[5] = (H[5] + f) >>> 0;
        H[6] = (H[6] + g) >>> 0; H[7] = (H[7] + h) >>> 0;
    }
    const result = new Uint8Array(32);
    const rv = new DataView(result.buffer);
    for (let i = 0; i < 8; i++) rv.setUint32(i * 4, H[i], false);
    return result;
}

function hashMD5(data, salt) {
    let msg = data instanceof Uint8Array ? data : toBytes(data);
    if (salt) {
        const s = salt instanceof Uint8Array ? salt : toBytes(salt);
        msg = mergeBytes(msg, s);
    }
    const K = new Uint32Array([
        0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
        0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
        0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
        0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
        0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
        0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
        0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
        0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
    ]);
    const S = [7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
        4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
    ];
    let [a0, b0, c0, d0] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476];
    const len = msg.length;
    const paddingLen = ((56 - (len + 1) % 64) + 64) % 64;
    const padded = new Uint8Array(len + 1 + paddingLen + 8);
    padded.set(msg);
    padded[len] = 0x80;
    const view = new DataView(padded.buffer);
    view.setUint32(padded.length - 8, (len * 8) >>> 0, true);
    view.setUint32(padded.length - 4, (len * 8 / 0x100000000) >>> 0, true);
    const rotl = (x, n) => (x << n) | (x >>> (32 - n));
    for (let i = 0; i < padded.length; i += 64) {
        const M = new Uint32Array(16);
        for (let j = 0; j < 16; j++) M[j] = view.getUint32(i + j * 4, true);
        let [A, B, C, D] = [a0, b0, c0, d0];
        for (let j = 0; j < 64; j++) {
            let F, g;
            if (j < 16) { F = (B & C) | (~B & D); g = j; }
            else if (j < 32) { F = (D & B) | (~D & C); g = (5 * j + 1) % 16; }
            else if (j < 48) { F = B ^ C ^ D; g = (3 * j + 5) % 16; }
            else { F = C ^ (B | ~D); g = (7 * j) % 16; }
            F = (F + A + K[j] + M[g]) >>> 0;
            A = D; D = C; C = B; B = (B + rotl(F, S[j])) >>> 0;
        }
        a0 = (a0 + A) >>> 0; b0 = (b0 + B) >>> 0;
        c0 = (c0 + C) >>> 0; d0 = (d0 + D) >>> 0;
    }
    const result = new Uint8Array(16);
    const rv = new DataView(result.buffer);
    rv.setUint32(0, a0, true); rv.setUint32(4, b0, true);
    rv.setUint32(8, c0, true); rv.setUint32(12, d0, true);
    return result;
}

function createRecursiveHash(key, underlyingHashFn) {
    const ipad = createBuffer(64, 0x36);
    const opad = createBuffer(64, 0x5c);
    const keyBuf = key instanceof Uint8Array ? key : toBytes(key);
    for (let i = 0; i < keyBuf.length; i++) {
        ipad[i] ^= keyBuf[i];
        opad[i] ^= keyBuf[i];
    }
    return (data) => underlyingHashFn(mergeBytes(opad, underlyingHashFn(mergeBytes(ipad, data))));
}

function deriveKey(key, path) {
    let fn = hashSHA256;
    fn = createRecursiveHash(toBytes("KDF"), fn);
    for (const p of path) fn = createRecursiveHash(p, fn);
    return fn(key);
}

function parseUUID(uuidStr) {
    const hex = uuidStr.replace(/-/g, '');
    const arr = new Uint8Array(16);
    for (let i = 0; i < 16; i++) arr[i] = parseInt(hex.substr(i * 2, 2), 16);
    return arr;
}

async function aesDecrypt(key, iv, data, aad) {
    const cryptoKey = await crypto.subtle.importKey('raw', key, { name: 'AES-GCM' }, false, ['decrypt']);
    const decrypted = await crypto.subtle.decrypt({ name: 'AES-GCM', iv, additionalData: aad || new Uint8Array(0), tagLength: 128 }, cryptoKey, data);
    return new Uint8Array(decrypted);
}

async function aesEncrypt(key, iv, data, aad) {
    const cryptoKey = await crypto.subtle.importKey('raw', key, { name: 'AES-GCM' }, false, ['encrypt']);
    const encrypted = await crypto.subtle.encrypt({ name: 'AES-GCM', iv, additionalData: aad || new Uint8Array(0), tagLength: 128 }, cryptoKey, data);
    return new Uint8Array(encrypted);
}

// ==================== ROUTE PARSING ====================
function parseRoute(pathname) {
    if (!pathname || pathname === '/') return null;
    
    const parts = pathname.substring(1).split('/');
    const command = parts[0];
    
    // Fixed regex: changed [d.] to [\d.] and corrected the pattern
    const directMatch = pathname.match(/^\/([\d.]+)[:=:-](\d+)$/);
    if (directMatch) {
        return directMatch[1] + ':' + directMatch[2];
    }
    
    // Fixed regex: removed extra slash, changed [d] to [\d]
    const proxyMatch = pathname.match(/^\/api\/(.+[:=-]\d+)$/);
    if (proxyMatch) {
        return proxyMatch[1];
    }
    
    return command;
}

async function handleReverseProxy(request, target) {
    const targetUrl = new URL(request.url);
    targetUrl.hostname = target;
    
    const modifiedRequest = new Request(targetUrl, request);
    modifiedRequest.headers.set("X-Forwarded-Host", request.headers.get("Host"));
    
    const response = await fetch(modifiedRequest);
    const newResponse = new Response(response.body, response);
    newResponse.headers.set("X-Proxied-By", "CF-Worker");
    
    return newResponse;
}

// ==================== PROTOCOL DETECTION & PARSING ====================
async function detectType(buffer) {
    // Check Type A
    if (buffer.byteLength >= DETECTION_PATTERNS.BUFFER_MIN_SIZE) {
        const delimiter = buffer.slice(DETECTION_PATTERNS.DELIMITER_OFFSET, DETECTION_PATTERNS.DELIMITER_OFFSET + 4);
        if (delimiter[0] === DETECTION_PATTERNS.DELIMITER_P1[0] && delimiter[1] === DETECTION_PATTERNS.DELIMITER_P1[1]) {
            if (DETECTION_PATTERNS.DELIMITER_P1_CHECK.includes(delimiter[2]) && 
                DETECTION_PATTERNS.DELIMITER_P1_CHECK.concat([0x04]).includes(delimiter[3])) {
                return TYPES.TYPE_A;
            }
        }
    }
    
    // Check Type B
    const uuidCheck = buffer.slice(1, 17);
    const hexString = bufferToHex(uuidCheck.buffer);
    if (DETECTION_PATTERNS.UUID_V4_REGEX.test(hexString)) {
        return TYPES.TYPE_B;
    }
    
    // Check Type D
    if (await isTypeD(buffer)) {
        return TYPES.TYPE_D;
    }
    
    // Default Type C
    return TYPES.TYPE_C;
}

async function isTypeD(buffer) {
    if (buffer.length < 42) return false;
    try {
        const uuidBytes = parseUUID(internalKey);
        const auth_id = buffer.subarray(0, 16);
        const len_encrypted = buffer.subarray(16, 34);
        const nonce = buffer.subarray(34, 42);
        const key = hashMD5(uuidBytes, toBytes("c48619fe-8f02-49e0-b9e9-edf763e17e21"));
        const header_length_key = deriveKey(key, [CRYPTO_SALT_1, auth_id, nonce]).subarray(0, 16);
        const header_length_nonce = deriveKey(key, [CRYPTO_SALT_2, auth_id, nonce]).subarray(0, 12);
        const decryptedLen = await aesDecrypt(header_length_key, header_length_nonce, len_encrypted, auth_id);
        const header_length = (decryptedLen[0] << 8) | decryptedLen[1];
        return header_length > 0 && header_length < 4096;
    } catch (e) {
        return false;
    }
}

async function parseTypeD(buffer) {
    const uuidBytes = parseUUID(internalKey);
    if (buffer.length < 16) throw new Error("Data too short");
    const auth_id = buffer.subarray(0, 16);
    let remaining = buffer.subarray(16);
    if (remaining.length < 18) throw new Error("Data too short");
    const len_encrypted = remaining.subarray(0, 18);
    remaining = remaining.subarray(18);
    if (remaining.length < 8) throw new Error("Data too short");
    const nonce = remaining.subarray(0, 8);
    remaining = remaining.subarray(8);
    const key = hashMD5(uuidBytes, toBytes("c48619fe-8f02-49e0-b9e9-edf763e17e21"));
    const mainKey = key;
    const header_length_key = deriveKey(key, [CRYPTO_SALT_1, auth_id, nonce]).subarray(0, 16);
    const header_length_nonce = deriveKey(key, [CRYPTO_SALT_2, auth_id, nonce]).subarray(0, 12);
    const decryptedLen = await aesDecrypt(header_length_key, header_length_nonce, len_encrypted, auth_id);
    const header_length = (decryptedLen[0] << 8) | decryptedLen[1];
    if (remaining.length < header_length + 16) throw new Error("Data too short");
    const cmd_encrypted = remaining.subarray(0, header_length + 16);
    const rawClientData = remaining.subarray(header_length + 16);
    const payload_key = deriveKey(mainKey, [CRYPTO_SALT_3, auth_id, nonce]).subarray(0, 16);
    const payload_nonce = deriveKey(mainKey, [CRYPTO_SALT_4, auth_id, nonce]).subarray(0, 12);
    const cmdBuf = await aesDecrypt(payload_key, payload_nonce, cmd_encrypted, auth_id);
    if (cmdBuf[0] !== 1) throw new Error("Invalid version");
    const iv = cmdBuf.subarray(1, 17);
    const keyResp = cmdBuf.subarray(17, 33);
    const responseAuth = cmdBuf[33];
    const command = cmdBuf[37];
    const portRemote = (cmdBuf[38] << 8) | cmdBuf[39];
    const addrType = cmdBuf[40];
    let addrEnd = 41, addressRemote = "";
    if (addrType === 1) {
        addressRemote = cmdBuf[41] + '.' + cmdBuf[42] + '.' + cmdBuf[43] + '.' + cmdBuf[44];
        addrEnd += 4;
    } else if (addrType === 2) {
        const len = cmdBuf[41];
        addressRemote = fromBytes(cmdBuf.subarray(42, 42 + len));
        addrEnd += 1 + len;
    } else if (addrType === 3) {
        const parts = [];
        for (let i = 0; i < 8; i++) parts.push(((cmdBuf[41 + i * 2] << 8) | cmdBuf[41 + i * 2 + 1]).toString(16));
        addressRemote = parts.join(':');
        addrEnd += 16;
    }
    const respKeyBase = hashSHA256(keyResp).subarray(0, 16);
    const respIvBase = hashSHA256(iv).subarray(0, 16);
    const length_key = deriveKey(respKeyBase, [CRYPTO_SALT_5]).subarray(0, 16);
    const length_iv = deriveKey(respIvBase, [CRYPTO_SALT_6]).subarray(0, 12);
    const encryptedLength = await aesEncrypt(length_key, length_iv, new Uint8Array([0, 4]));
    const payload_key_resp = deriveKey(respKeyBase, [CRYPTO_SALT_7]).subarray(0, 16);
    const payload_iv_resp = deriveKey(respIvBase, [CRYPTO_SALT_8]).subarray(0, 12);
    const encryptedHeaderPayload = await aesEncrypt(payload_key_resp, payload_iv_resp, new Uint8Array([responseAuth, 0, 0, 0]));
    return {
        hasError: false,
        addressRemote,
        portRemote,
        rawClientData,
        version: mergeBytes(encryptedLength, encryptedHeaderPayload),
        isUDP: portRemote === DNS_PORT
    };
}

function parseTypeC(buffer) {
    const view = new DataView(buffer.buffer, buffer.byteOffset, buffer.byteLength);
    const addressType = view.getUint8(0);
    let addressLength = 0, addressValueIndex = 1, addressValue = "";
    switch (addressType) {
        case ADDRESS_TYPES.IPV4:
            addressLength = 4;
            addressValue = new Uint8Array(buffer.slice(addressValueIndex, addressValueIndex + addressLength)).join(".");
            break;
        case ADDRESS_TYPES.DOMAIN_ALT:
            addressLength = buffer[addressValueIndex];
            addressValueIndex += 1;
            addressValue = fromBytes(buffer.slice(addressValueIndex, addressValueIndex + addressLength));
            break;
        case ADDRESS_TYPES.IPV6:
            addressLength = 16;
            const dv = new DataView(buffer.slice(addressValueIndex, addressValueIndex + addressLength).buffer);
            const ipv6 = [];
            for (let i = 0; i < 8; i++) ipv6.push(dv.getUint16(i * 2).toString(16));
            addressValue = ipv6.join(":");
            break;
        default:
            return { hasError: true, message: 'Invalid addressType: ' + addressType };
    }
    if (!addressValue) return { hasError: true, message: 'Destination address empty' };
    const portIndex = addressValueIndex + addressLength;
    const portBuffer = buffer.slice(portIndex, portIndex + 2);
    const portRemote = new DataView(portBuffer.buffer, portBuffer.byteOffset, 2).getUint16(0);
    return {
        hasError: false,
        addressRemote: addressValue,
        addressType,
        portRemote,
        rawDataIndex: portIndex + 2,
        rawClientData: buffer.slice(portIndex + 2),
        version: null,
        isUDP: portRemote == DNS_PORT
    };
}

function parseTypeB(buffer) {
    const version = buffer[0];
    let isUDP = false;
    const optLength = buffer[17];
    const cmd = buffer[18 + optLength];
    if (cmd === COMMAND_TYPES.TCP) {
        // TCP
    } else if (cmd === COMMAND_TYPES.UDP) {
        isUDP = true;
    } else {
        return { hasError: true, message: 'Command ' + cmd + ' not supported' };
    }
    const portIndex = 18 + optLength + 1;
    const portBuffer = buffer.slice(portIndex, portIndex + 2);
    const portRemote = new DataView(portBuffer.buffer, portBuffer.byteOffset, 2).getUint16(0);
    let addressIndex = portIndex + 2;
    const addressType = buffer[addressIndex];
    let addressLength = 0, addressValueIndex = addressIndex + 1, addressValue = "";
    switch (addressType) {
        case ADDRESS_TYPES.IPV4:
            addressLength = 4;
            addressValue = new Uint8Array(buffer.slice(addressValueIndex, addressValueIndex + addressLength)).join(".");
            break;
        case ADDRESS_TYPES.DOMAIN:
            addressLength = buffer[addressValueIndex];
            addressValueIndex += 1;
            addressValue = fromBytes(buffer.slice(addressValueIndex, addressValueIndex + addressLength));
            break;
        case ADDRESS_TYPES.IPV6:
            addressLength = 16;
            const dv = new DataView(buffer.slice(addressValueIndex, addressValueIndex + addressLength).buffer);
            const ipv6 = [];
            for (let i = 0; i < 8; i++) ipv6.push(dv.getUint16(i * 2).toString(16));
            addressValue = ipv6.join(":");
            break;
        default:
            return { hasError: true, message: 'Invalid addressType: ' + addressType };
    }
    if (!addressValue) return { hasError: true, message: 'addressValue is empty' };
    return {
        hasError: false,
        addressRemote: addressValue,
        addressType,
        portRemote,
        rawDataIndex: addressValueIndex + addressLength,
        rawClientData: buffer.slice(addressValueIndex + addressLength),
        version: new Uint8Array([version, 0]),
        isUDP
    };
}

function parseTypeA(buffer) {
    const dataBuffer = buffer.slice(58);
    if (dataBuffer.byteLength < 6) return { hasError: true, message: "Invalid request data" };
    let isUDP = false;
    const view = new DataView(dataBuffer.buffer, dataBuffer.byteOffset, dataBuffer.byteLength);
    const cmd = view.getUint8(0);
    if (cmd == COMMAND_TYPES.UDP_ALT) isUDP = true;
    else if (cmd != COMMAND_TYPES.TCP) throw new Error("Unsupported command type!");
    let addressType = view.getUint8(1);
    let addressLength = 0, addressValueIndex = 2, addressValue = "";
    switch (addressType) {
        case ADDRESS_TYPES.IPV4:
            addressLength = 4;
            addressValue = new Uint8Array(dataBuffer.slice(addressValueIndex, addressValueIndex + addressLength)).join(".");
            break;
        case ADDRESS_TYPES.DOMAIN_ALT:
            addressLength = dataBuffer[addressValueIndex];
            addressValueIndex += 1;
            addressValue = fromBytes(dataBuffer.slice(addressValueIndex, addressValueIndex + addressLength));
            break;
        case ADDRESS_TYPES.IPV6:
            addressLength = 16;
            const dv = new DataView(dataBuffer.slice(addressValueIndex, addressValueIndex + addressLength).buffer);
            const ipv6 = [];
            for (let i = 0; i < 8; i++) ipv6.push(dv.getUint16(i * 2).toString(16));
            addressValue = ipv6.join(":");
            break;
        default:
            return { hasError: true, message: 'Invalid addressType: ' + addressType };
    }
    if (!addressValue) return { hasError: true, message: 'Address is empty' };
    const portIndex = addressValueIndex + addressLength;
    const portBuffer = dataBuffer.slice(portIndex, portIndex + 2);
    const portRemote = new DataView(portBuffer.buffer, portBuffer.byteOffset, 2).getUint16(0);
    return {
        hasError: false,
        addressRemote: addressValue,
        addressType,
        portRemote,
        rawDataIndex: portIndex + 4,
        rawClientData: dataBuffer.slice(portIndex + 4),
        version: null,
        isUDP
    };
}

// ==================== WEBSOCKET HANDLER ====================
function safeClose(socket) {
    try {
        if (socket.readyState === WS_READY_STATE_OPEN || socket.readyState === WS_READY_STATE_CLOSING) socket.close();
    } catch (e) {
        console.error("safeClose error", e);
    }
}

function createReadableStream(wsServer, earlyDataHeader, log) {
    let cancelFlag = false;
    return new ReadableStream({
        start(controller) {
            wsServer.addEventListener("message", (event) => {
                if (!cancelFlag) controller.enqueue(event.data);
            });
            wsServer.addEventListener("close", () => {
                safeClose(wsServer);
                if (!cancelFlag) controller.close();
            });
            wsServer.addEventListener("error", (err) => {
                log("ws error");
                controller.error(err);
            });
            const { earlyData, error } = base64ToBuffer(earlyDataHeader);
            if (error) {
                controller.error(error);
            } else if (earlyData) {
                controller.enqueue(earlyData);
            }
        },
        cancel(reason) {
            if (!cancelFlag) {
                log('Stream canceled: ' + reason);
                cancelFlag = true;
                safeClose(wsServer);
            }
        },
    });
}

async function forwardToRemote(remoteSocket, webSocket, responseHeader, retry, log) {
    let header = responseHeader, hasData = false;
    await remoteSocket.readable.pipeTo(new WritableStream({
        async write(chunk, controller) {
            hasData = true;
            if (webSocket.readyState !== WS_READY_STATE_OPEN) controller.error("ws closed");
            if (header) {
                webSocket.send(await new Blob([header, chunk]).arrayBuffer());
                header = null;
            } else webSocket.send(chunk);
        },
        close() { log('remote closed, hasData: ' + hasData); },
        abort(reason) { console.error('remote abort', reason); },
    })).catch((error) => {
        console.error('forward error', error.stack || error);
        safeClose(webSocket);
    });
    if (!hasData && retry) {
        log('retrying');
        retry();
    }
}

async function handleTCP(remoteSocket, addressRemote, portRemote, rawData, webSocket, responseHeader, log) {
    async function connectAndWrite(address, port) {
        const tcpSocket = connect({ hostname: address, port });
        remoteSocket.value = tcpSocket;
        log('connected to ' + address + ':' + port);
        const writer = tcpSocket.writable.getWriter();
        await writer.write(rawData);
        writer.releaseLock();
        return tcpSocket;
    }
    async function retry() {
        const targetHost = (routeConfig ? routeConfig.split(/[:=-]/)[0] : addressRemote);
        const targetPort = (routeConfig ? parseInt(routeConfig.split(/[:=-]/)[1]) : portRemote);
        const tcpSocket = await connectAndWrite(targetHost, targetPort);
        tcpSocket.closed.catch(e => console.log("retry error", e)).finally(() => safeClose(webSocket));
        forwardToRemote(tcpSocket, webSocket, responseHeader, null, log);
    }
    const tcpSocket = await connectAndWrite(addressRemote, portRemote);
    forwardToRemote(tcpSocket, webSocket, responseHeader, retry, log);
}

async function handleUDP(webSocket, responseHeader, log) {
    let headerSent = false;
    const transformStream = new TransformStream({
        transform(chunk, controller) {
            for (let index = 0; index < chunk.byteLength;) {
                const lengthBuffer = chunk.slice(index, index + 2);
                const packetLen = new DataView(lengthBuffer.buffer, lengthBuffer.byteOffset, 2).getUint16(0);
                controller.enqueue(new Uint8Array(chunk.slice(index + 2, index + 2 + packetLen)));
                index += 2 + packetLen;
            }
        },
    });
    transformStream.readable.pipeTo(new WritableStream({
        async write(chunk) {
            const resp = await fetch("https://1.1.1.1/dns-query", {
                method: "POST",
                headers: { "content-type": "application/dns-message" },
                body: chunk
            });
            const result = await resp.arrayBuffer();
            const size = result.byteLength;
            const sizeBuffer = new Uint8Array([(size >> 8) & 0xff, size & 0xff]);
            if (webSocket.readyState === WS_READY_STATE_OPEN) {
                log('DNS success, length: ' + size);
                if (headerSent) webSocket.send(await new Blob([sizeBuffer, result]).arrayBuffer());
                else {
                    webSocket.send(await new Blob([responseHeader, sizeBuffer, result]).arrayBuffer());
                    headerSent = true;
                }
            }
        },
    })).catch(e => log("DNS error: " + e));
    const writer = transformStream.writable.getWriter();
    return { write(chunk) { writer.write(chunk); } };
}

async function wsHandler(request) {
    const wsPair = new WebSocketPair();
    const [client, server] = Object.values(wsPair);
    server.accept();

    let addrLog = "", portLog = "";
    const log = (info, event) => console.log('[' + addrLog + ':' + portLog + '] ' + info, event || "");

    const earlyData = request.headers.get("sec-websocket-protocol") || "";
    const readableStream = createReadableStream(server, earlyData, log);

    let remoteSocket = { value: null };
    let udpWriter = null, isDnsMode = false;

    readableStream.pipeTo(new WritableStream({
        async write(chunk, controller) {
            if (isDnsMode && udpWriter) return udpWriter(chunk);
            if (remoteSocket.value) {
                const writer = remoteSocket.value.writable.getWriter();
                await writer.write(chunk);
                writer.releaseLock();
                return;
            }

            const dataChunk = new Uint8Array(chunk);
            const protocol = await detectType(dataChunk);
            let header;

            if (protocol === TYPES.TYPE_A) {
                header = parseTypeA(dataChunk);
            } else if (protocol === TYPES.TYPE_B) {
                header = parseTypeB(dataChunk);
            } else if (protocol === TYPES.TYPE_D) {
                header = await parseTypeD(dataChunk);
            } else {
                header = parseTypeC(dataChunk);
            }

            addrLog = header.addressRemote;
            portLog = header.portRemote + ' -> ' + (header.isUDP ? "UDP" : "TCP");
            if (header.hasError) throw new Error(header.message);

            if (header.isUDP) {
                if (header.portRemote === DNS_PORT) isDnsMode = true;
                else throw new Error("UDP only for DNS port 53");
            }

            if (isDnsMode) {
                const { write } = await handleUDP(server, header.version, log);
                udpWriter = write;
                udpWriter(header.rawClientData);
                return;
            }

            handleTCP(remoteSocket, header.addressRemote, header.portRemote,
                header.rawClientData, server, header.version, log);
        },
        close() { log('stream closed'); },
        abort(reason) { log('stream aborted', JSON.stringify(reason)); },
    })).catch((err) => log("pipe error", err));

    return new Response(null, { status: 101, webSocket: client });
}

// ==================== MAIN HANDLER ====================
export default {
    async fetch(request, env, ctx) {
        try {
            const url = new URL(request.url);
            const upgradeHeader = request.headers.get("Upgrade");
            
            if (upgradeHeader === "websocket") {
                const route = parseRoute(url.pathname);
                if (route) {
                    routeConfig = route;
                }
                return await wsHandler(request);
            }
            
            const targetProxy = env.REVERSE_PROXY_TARGET || "countdownaio.netlify.app";
            return await handleReverseProxy(request, targetProxy);
            
        } catch (err) {
            return new Response('Error: ' + err.toString(), { status: 500 });
        }
    },
};
