//! Reads NTP packets with ntpd-rs's packet parser, `NtpPacket::deserialize`
//! in the ntp-proto crate, for tests/run_tests.py.
//!
//! Each line of standard input is one UDP payload in lower-case hex (`-`
//! for none). For each, one line of standard output:
//!
//!   FAIL ERROR             the parser refused it, with its error
//!   OK V LI MODE STRATUM POLL PRECISION DELAY DISPERSION REFID REF ORG REC XMT FIELDS MAC NTS
//!
//! - V, LI, MODE, STRATUM, POLL, PRECISION: decimal, as the parser read
//!   them (POLL and PRECISION signed);
//! - DELAY, DISPERSION: the 32 bits of each in NTP short format, decimal.
//!   The crate keeps them only as a duration, so they are taken from the
//!   header its own writer, `NtpPacket::serialize`, writes for the packet;
//! - REFID: the reference ID, decimal; REF ORG REC XMT: the four
//!   timestamps, decimal, each its 64 bits as the crate keeps them;
//! - FIELDS: `-`, or each extension field as TYPE:HEX, comma separated,
//!   TYPE in decimal and HEX its value and padding as the crate gives
//!   them (`-` for none, `*` for an NTS authenticator field, whose
//!   contents the crate does not give without a key);
//! - MAC: `-`, or the key identifier and digest in hex;
//! - NTS: `nts-unverified` when the parser gave the packet back with a
//!   decryption error (an NTS authenticator field it had no key for),
//!   else `-`.
//!
//! The parser is given no key (`NoCipher`).

use std::fmt::Write as _;
use std::io::{BufRead, Cursor, Write};

use ntp_proto::{NoCipher, NtpPacket, NtpVersion, PacketParsingError};

fn hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "-".to_string();
    }
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        write!(s, "{b:02x}").unwrap();
    }
    s
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if s == "-" {
        return Some(Vec::new());
    }
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

/// The number in `NAME(n)` within a Debug string, after `key`.
fn debug_number(text: &str, key: &str, name: &str) -> String {
    let start = text.find(key).expect("field in Debug output") + key.len();
    let rest = &text[start..];
    let open = rest.find(name).expect("type name") + name.len() + 1;
    let close = rest[open..].find(')').expect("closing parenthesis") + open;
    rest[open..close].to_string()
}

/// The bytes of a Debug list, `[1, 2, 3]`.
fn debug_bytes(text: &str) -> Vec<u8> {
    let open = text.find('[').expect("a list") + 1;
    let close = text[open..].find(']').expect("end of list") + open;
    text[open..close]
        .split(", ")
        .filter(|s| !s.is_empty())
        .map(|b| b.parse().expect("a byte"))
        .collect()
}

/// An extension field as TYPE:HEX, from its Debug output: the crate
/// exports its type only to fuzzers, so its variants cannot be named
/// here.
fn field(debug: &str) -> String {
    if let Some(rest) = debug.strip_prefix("UniqueIdentifier(") {
        format!("{}:{}", 0x0104, hex(&debug_bytes(rest)))
    } else if let Some(rest) = debug.strip_prefix("NtsCookie(") {
        format!("{}:{}", 0x0204, hex(&debug_bytes(rest)))
    } else if let Some(rest) = debug.strip_prefix("NtsCookiePlaceholder { body_length: ") {
        let n: usize = rest.trim_end_matches(" }").parse().expect("a length");
        format!("{}:{}", 0x0304, hex(&vec![0u8; n]))
    } else if debug.starts_with("InvalidNtsEncryptedField") {
        format!("{}:*", 0x0404)
    } else if let Some(rest) = debug.strip_prefix("Unknown { typeid: ") {
        let t: u16 = rest[..rest.find(',').expect("a comma")].parse().expect("a type");
        format!("{}:{}", t, hex(&debug_bytes(rest)))
    } else {
        format!("?{}", debug.replace(' ', "_"))
    }
}

fn show(packet: &NtpPacket<'_>, nts: bool) -> String {
    let version = match packet.version() {
        NtpVersion::V3 => 3,
        NtpVersion::V4 => 4,
        NtpVersion::V5 => return format!("V5 {}", format!("{packet:?}").replace(' ', "_")),
    };
    let debug = format!("{:?}", packet.header());
    // The header as the crate's own writer writes it, for the two
    // short-format fields.
    let mut buffer = vec![0u8; 1 << 17];
    let mut cursor = Cursor::new(buffer.as_mut_slice());
    let _ = packet.serialize(&mut cursor, &NoCipher, None);
    let w = cursor.into_inner();
    let delay = u32::from_be_bytes(w[4..8].try_into().unwrap());
    let dispersion = u32::from_be_bytes(w[8..12].try_into().unwrap());
    let leap = match packet.leap() {
        ntp_proto::NtpLeapIndicator::NoWarning => 0,
        ntp_proto::NtpLeapIndicator::Leap61 => 1,
        ntp_proto::NtpLeapIndicator::Leap59 => 2,
        ntp_proto::NtpLeapIndicator::Unknown | ntp_proto::NtpLeapIndicator::Unsynchronized => 3,
    };
    let mode = match packet.mode() {
        ntp_proto::NtpAssociationMode::Reserved => 0,
        ntp_proto::NtpAssociationMode::SymmetricActive => 1,
        ntp_proto::NtpAssociationMode::SymmetricPassive => 2,
        ntp_proto::NtpAssociationMode::Client => 3,
        ntp_proto::NtpAssociationMode::Server => 4,
        ntp_proto::NtpAssociationMode::Broadcast => 5,
        ntp_proto::NtpAssociationMode::Control => 6,
        ntp_proto::NtpAssociationMode::Private => 7,
    };
    let fields: Vec<String> = packet
        .authenticated_extension_fields()
        .chain(packet.untrusted_extension_fields())
        .map(|ef| field(&format!("{ef:?}")))
        .collect();
    let fields = if fields.is_empty() { "-".to_string() } else { fields.join(",") };
    // The MAC is not reachable through the crate's API but its Debug
    // output: `mac: None` or `mac: Some(Mac { keyid: K, mac: [..] })`.
    let all = format!("{packet:?}");
    let key = "mac: Some(Mac { keyid: ";
    let mac = match all.rfind(key) {
        None => {
            assert!(all.ends_with("mac: None }"), "a MAC or none in Debug output");
            "-".to_string()
        }
        Some(i) => {
            let m = &all[i + key.len()..];
            let keyid: u32 = m[..m.find(',').expect("a comma")].parse().expect("a key ID");
            let mut bytes = keyid.to_be_bytes().to_vec();
            bytes.extend(debug_bytes(m));
            hex(&bytes)
        }
    };
    format!(
        "OK {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {}",
        version,
        leap,
        mode,
        packet.stratum(),
        packet.poll().as_log(),
        packet.precision(),
        delay,
        dispersion,
        debug_number(&debug, "reference_id: ", "ReferenceId"),
        debug_number(&debug, "reference_timestamp: ", "NtpTimestamp"),
        debug_number(&debug, "origin_timestamp: ", "NtpTimestamp"),
        debug_number(&debug, "receive_timestamp: ", "NtpTimestamp"),
        debug_number(&debug, "transmit_timestamp: ", "NtpTimestamp"),
        fields,
        mac,
        if nts { "nts-unverified" } else { "-" }
    )
}

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    for line in stdin.lock().lines() {
        let line = line.expect("a line of input");
        let answer = match unhex(line.trim_end_matches('\r')) {
            None => "error".to_string(),
            Some(data) => match NtpPacket::deserialize(&data, &NoCipher) {
                Ok((packet, _)) => show(&packet, false),
                Err(PacketParsingError::DecryptError(packet)) => show(&packet, true),
                Err(e) => format!("FAIL {e:?}"),
            },
        };
        writeln!(out, "{answer}").unwrap();
    }
    out.flush().unwrap();
}
