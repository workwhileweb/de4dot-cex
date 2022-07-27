﻿/*
    Copyright (C) 2011-2015 de4dot@gmail.com

    This file is part of de4dot.

    de4dot is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    de4dot is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with de4dot.  If not, see <http://www.gnu.org/licenses/>.
*/

using System;
using System.IO;
using System.Security.Cryptography;
using dnlib.DotNet;

namespace de4dot.code.deobfuscators.ILProtector {
	class RuntimeFileInfo {
		public MethodDef ProtectMethod { get; private set; }
		public string PathName { get; private set; }
		public string Name { get; private set; }
		Version runtimeVersion;
		bool runtimeVersionInitialized;

		class VersionInfo {
			public Version Version { get; private set; }
			public uint FileOffset { get; private set; }
			public byte[] Hash { get; private set; }

			public VersionInfo(Version version, byte[] hash) {
				this.Version = version;
				this.Hash = hash;
			}
		}

		static readonly VersionInfo[] versionInfo32 = new VersionInfo[] {
			new VersionInfo(new Version(1, 0, 7, 0), new byte[] { 0x1B, 0x7A, 0x48, 0x9E, 0x70, 0x69, 0x3C, 0x51, 0xDB, 0x3E, 0xD8, 0x09, 0x71, 0x1F, 0x16, 0x33 }),
			new VersionInfo(new Version(1, 0, 7, 1), new byte[] { 0xD2, 0x76, 0x37, 0xA2, 0xE4, 0xCC, 0x66, 0xAB, 0x6A, 0x72, 0x45, 0x25, 0x06, 0x64, 0x05, 0xD7 }),
			new VersionInfo(new Version(1, 0, 8, 0), new byte[] { 0x0B, 0x3D, 0xFD, 0xB3, 0x8B, 0xCF, 0x59, 0x42, 0x9C, 0x4C, 0x2B, 0x43, 0xA4, 0x22, 0x91, 0xB0 }),
			new VersionInfo(new Version(2, 0, 0, 0), new byte[] { 0xC5, 0x8A, 0x92, 0x92, 0xBD, 0xA4, 0x6D, 0xF2, 0xEA, 0xF8, 0x4F, 0x79, 0x89, 0xF2, 0x44, 0x38 }),
			new VersionInfo(new Version(2, 0, 1, 0), new byte[] { 0xFD, 0x79, 0x53, 0x6C, 0xDA, 0x10, 0x3F, 0x29, 0xBF, 0x52, 0x4B, 0x70, 0xB2, 0xFF, 0x55, 0x25 }),
			new VersionInfo(new Version(2, 0, 2, 0), new byte[] { 0xED, 0xC2, 0xB2, 0x07, 0x1F, 0x1A, 0xF0, 0x4D, 0x9B, 0x37, 0x6F, 0x10, 0x7A, 0xDA, 0xA2, 0xED }),
			new VersionInfo(new Version(2, 0, 3, 0), new byte[] { 0xF3, 0xD8, 0x48, 0x69, 0x2B, 0x39, 0x99, 0x48, 0xB7, 0x8D, 0x0D, 0x72, 0xC5, 0xE4, 0xF5, 0x6D }),
			new VersionInfo(new Version(2, 0, 4, 0), new byte[] { 0xBC, 0x39, 0x58, 0x38, 0x5C, 0x2F, 0x5A, 0x50, 0xCF, 0xF7, 0x47, 0xC7, 0xEC, 0x52, 0xC6, 0xD0 }),
			new VersionInfo(new Version(2, 0, 5, 0), new byte[] { 0x90, 0x42, 0x0F, 0xB5, 0x84, 0x09, 0x90, 0xE5, 0xD8, 0x10, 0xF1, 0xAF, 0xF5, 0xBC, 0xA5, 0xF8 }),
			new VersionInfo(new Version(2, 0, 6, 0), new byte[] { 0xD1, 0x8D, 0x0C, 0x3C, 0x51, 0xBD, 0x36, 0x37, 0x17, 0xAB, 0xEC, 0x92, 0x19, 0x1B, 0xB0, 0xD6 }),
			new VersionInfo(new Version(2, 0, 7, 0), new byte[] { 0x02, 0xD1, 0x75, 0x77, 0x12, 0x6D, 0x4E, 0x86, 0x90, 0x34, 0x6A, 0xBB, 0x56, 0x0E, 0x6A, 0xEA }),
			new VersionInfo(new Version(2, 0, 7, 5), new byte[] { 0x7D, 0x5C, 0xBE, 0x21, 0x0B, 0xA9, 0x15, 0xFF, 0xE6, 0xC9, 0xD5, 0xFD, 0x7C, 0xA0, 0xAA, 0xC1 }),
			new VersionInfo(new Version(2, 0, 7, 6), new byte[] { 0x0D, 0x03, 0xB7, 0x1A, 0x74, 0x8E, 0x6B, 0x94, 0x2B, 0xD4, 0x33, 0x24, 0x49, 0xF8, 0x38, 0xD2 }),
			new VersionInfo(new Version(2, 0, 8, 0), new byte[] { 0xE6, 0xD6, 0x07, 0x89, 0x03, 0xA8, 0xE3, 0xD7, 0x86, 0x5A, 0x3D, 0xC2, 0x86, 0xF5, 0x0F, 0x67 }),
			new VersionInfo(new Version(2, 0, 8, 5), new byte[] { 0xFC, 0x79, 0x83, 0x61, 0xD2, 0x99, 0x8E, 0xE8, 0x2C, 0x5F, 0x14, 0xBA, 0xCB, 0xB9, 0x28, 0xF2 }),
			new VersionInfo(new Version(2, 0, 9, 0), new byte[] { 0x7A, 0x88, 0xD8, 0xC3, 0xB8, 0x77, 0xAA, 0x13, 0xC0, 0x6C, 0x43, 0x88, 0x0D, 0x66, 0xFE, 0x7A }),
			new VersionInfo(new Version(2, 0, 10, 0), new byte[] { 0xE5, 0x8E, 0xEB, 0x26, 0x1A, 0x1C, 0x44, 0xA8, 0xFF, 0x88, 0x14, 0xE7, 0x38, 0x13, 0xE5, 0x6D }),
			new VersionInfo(new Version(2, 0, 11, 0), new byte[] { 0x67, 0xB8, 0xF7, 0x15, 0x70, 0x1D, 0xF2, 0x57, 0x00, 0x42, 0xF3, 0xA4, 0x83, 0x07, 0x62, 0xA3 }),
			new VersionInfo(new Version(2, 0, 11, 1), new byte[] { 0x2E, 0xC9, 0x53, 0xA0, 0x3C, 0x9B, 0x08, 0xDA, 0x88, 0x84, 0x37, 0xFC, 0x07, 0xAE, 0x8B, 0xEC }),
			new VersionInfo(new Version(2, 0, 12, 0), new byte[] { 0x63, 0x8B, 0x5C, 0xE9, 0x89, 0x83, 0x57, 0x9D, 0xDC, 0xC3, 0xBD, 0xD9, 0xDB, 0x54, 0xBE, 0x66 }),
			new VersionInfo(new Version(2, 0, 12, 2), new byte[] { 0xD5, 0x46, 0x38, 0xC7, 0x48, 0xF6, 0x3C, 0x1C, 0x1E, 0x7F, 0x3B, 0x7B, 0x5B, 0xE0, 0x49, 0x46 }),
			new VersionInfo(new Version(2, 0, 12, 3), new byte[] { 0x35, 0xA3, 0x53, 0xE9, 0x9E, 0x30, 0x6E, 0x9C, 0x0F, 0x46, 0x20, 0x9A, 0x91, 0xD2, 0x95, 0x18 }),
			new VersionInfo(new Version(2, 0, 13, 0), new byte[] { 0x66, 0x21, 0xA1, 0x1F, 0x8F, 0x4A, 0xD2, 0xF8, 0x68, 0xEE, 0xD5, 0xD9, 0xC8, 0xB8, 0x17, 0xC7 }),
			new VersionInfo(new Version(2, 0, 13, 1), new byte[] { 0xDF, 0x7A, 0xBF, 0x8B, 0xAD, 0x2B, 0x94, 0x6F, 0x37, 0xD9, 0x4B, 0xFC, 0x42, 0x7F, 0x0B, 0x37 }),
		};

		static readonly VersionInfo[] versionInfo64 = new VersionInfo[] {
			// No sig for 1.0.7.0 x64 since I don't have it yet.
			new VersionInfo(new Version(1, 0, 7, 1), new byte[] { 0x8E, 0xB4, 0x61, 0x12, 0xDF, 0x76, 0x6F, 0xAB, 0xF0, 0x2C, 0x7A, 0x3A, 0x0D, 0x71, 0xE8, 0xB0 }),
			new VersionInfo(new Version(1, 0, 8, 0), new byte[] { 0x04, 0xB1, 0xDA, 0x92, 0xE7, 0x59, 0x54, 0x82, 0x0F, 0x46, 0xD6, 0x08, 0xA2, 0x69, 0xB7, 0x75 }),
			new VersionInfo(new Version(2, 0, 0, 0), new byte[] { 0xC7, 0xD9, 0x62, 0x7E, 0xEC, 0x6D, 0x10, 0x8A, 0xBF, 0x71, 0x7A, 0x4C, 0xC0, 0x3E, 0xAE, 0x9E }),
			new VersionInfo(new Version(2, 0, 1, 0), new byte[] { 0xD3, 0xCF, 0x89, 0x80, 0xFD, 0xB7, 0x38, 0xC2, 0x3C, 0xDF, 0x4E, 0x9D, 0xCE, 0xDD, 0x95, 0xDE }),
			new VersionInfo(new Version(2, 0, 2, 0), new byte[] { 0x44, 0xB7, 0xBA, 0xF9, 0x0A, 0x5B, 0xD6, 0xE7, 0xBE, 0x7A, 0x47, 0x82, 0x3B, 0x24, 0xB3, 0x73 }),
			new VersionInfo(new Version(2, 0, 3, 0), new byte[] { 0x8D, 0x25, 0x16, 0x40, 0xB6, 0xCF, 0x54, 0xF8, 0x78, 0xBE, 0x3A, 0xE5, 0x3D, 0x5E, 0xF9, 0x60 }),
			new VersionInfo(new Version(2, 0, 4, 0), new byte[] { 0x7F, 0x49, 0xEA, 0x93, 0x8E, 0x81, 0xFC, 0xF5, 0x56, 0x94, 0x73, 0xA8, 0x52, 0x61, 0x79, 0x60 }),
			new VersionInfo(new Version(2, 0, 5, 0), new byte[] { 0x08, 0xDB, 0xA2, 0x8E, 0xD7, 0x27, 0xBB, 0xD0, 0x69, 0xF5, 0x63, 0x28, 0x46, 0xBF, 0xBB, 0xB3 }),
			new VersionInfo(new Version(2, 0, 6, 0), new byte[] { 0x09, 0xFC, 0x92, 0x18, 0xC8, 0x34, 0xD6, 0x55, 0xE3, 0x7C, 0xA5, 0xCB, 0x15, 0x28, 0x59, 0x94 }),
			new VersionInfo(new Version(2, 0, 7, 0), new byte[] { 0x7B, 0x36, 0x68, 0xA0, 0x9E, 0xCB, 0xB9, 0x73, 0x5B, 0x1A, 0xAC, 0x50, 0x7E, 0x59, 0x1C, 0xB7 }),
			new VersionInfo(new Version(2, 0, 7, 5), new byte[] { 0x14, 0x13, 0x30, 0x60, 0x1A, 0xB0, 0x6F, 0x37, 0x82, 0xE3, 0x67, 0x16, 0x6C, 0x62, 0x30, 0x16 }),
			new VersionInfo(new Version(2, 0, 7, 6), new byte[] { 0x98, 0xDE, 0x41, 0x4B, 0x15, 0x2C, 0xF7, 0x34, 0x2A, 0xEF, 0xE3, 0x91, 0x07, 0x7F, 0x0F, 0xE7 }),
			new VersionInfo(new Version(2, 0, 8, 0), new byte[] { 0x21, 0x40, 0xED, 0xC6, 0xA2, 0x13, 0x3D, 0xCA, 0x22, 0x11, 0x02, 0x75, 0xFC, 0xE6, 0x3A, 0x51 }),
			new VersionInfo(new Version(2, 0, 8, 5), new byte[] { 0xF5, 0x67, 0xC1, 0x44, 0xF6, 0x2F, 0xBA, 0x01, 0xA3, 0x01, 0x91, 0x60, 0xDF, 0x99, 0xAB, 0x0C }),
			new VersionInfo(new Version(2, 0, 9, 0), new byte[] { 0x04, 0x17, 0xF3, 0xEA, 0x97, 0x24, 0x48, 0xC0, 0x01, 0x2E, 0x45, 0x80, 0x9D, 0x5B, 0x7C, 0xDF }),
			new VersionInfo(new Version(2, 0, 10, 0), new byte[] { 0xD8, 0x79, 0x05, 0xC9, 0x2D, 0xA6, 0x5B, 0x7D, 0xEE, 0xA6, 0x13, 0x25, 0x7D, 0x29, 0x73, 0xB4 }),
			new VersionInfo(new Version(2, 0, 11, 0), new byte[] { 0x49, 0xAD, 0x40, 0x10, 0xD4, 0x03, 0x04, 0xB4, 0x3C, 0xD2, 0x36, 0x67, 0x38, 0x62, 0x9C, 0xE8 }),
			new VersionInfo(new Version(2, 0, 11, 1), new byte[] { 0x1D, 0x6C, 0xB6, 0xC8, 0xB3, 0x07, 0x53, 0x24, 0x6F, 0xC0, 0xF3, 0x4F, 0x5E, 0x8B, 0x9F, 0xD1 }),
			new VersionInfo(new Version(2, 0, 12, 0), new byte[] { 0x5F, 0x42, 0xA5, 0x6C, 0x19, 0xC6, 0x73, 0x9E, 0xE6, 0x74, 0x62, 0x3B, 0x8A, 0x51, 0xBB, 0x93 }),
			new VersionInfo(new Version(2, 0, 12, 2), new byte[] { 0x10, 0x91, 0xED, 0x05, 0x9C, 0x31, 0x0B, 0x63, 0x76, 0xD7, 0x4A, 0xEC, 0xDE, 0x99, 0x6D, 0xD0 }),
			new VersionInfo(new Version(2, 0, 12, 3), new byte[] { 0x38, 0x86, 0xE0, 0xBF, 0xC6, 0x64, 0xB9, 0xA0, 0x07, 0xED, 0xDB, 0x02, 0x40, 0xD0, 0x57, 0xE8 }),
			new VersionInfo(new Version(2, 0, 13, 0), new byte[] { 0xF0, 0x13, 0xC4, 0x6F, 0x31, 0x0F, 0x61, 0xEA, 0x89, 0x1E, 0x8A, 0x95, 0x8C, 0xBE, 0x2E, 0x44 }),
			new VersionInfo(new Version(2, 0, 13, 1), new byte[] { 0xD4, 0x71, 0x75, 0xE2, 0xB1, 0xA5, 0xAE, 0xF5, 0x32, 0xD7, 0x72, 0xDE, 0x93, 0xDC, 0x0B, 0x68 }),
		};

		public RuntimeFileInfo(MethodDef protectMethod) {
			this.ProtectMethod = protectMethod;
			Name = !protectMethod.HasImplMap ? "<<UNKNOWN_NAME>>" : protectMethod.ImplMap.Module.Name.String;
			PathName = Path.Combine(Path.GetDirectoryName(Utils.GetFullPath(protectMethod.Module.Location)), Name);
		}

		public Version GetVersion() {
			if (runtimeVersionInitialized)
				return runtimeVersion;
			runtimeVersion = GetVersion2();
			runtimeVersionInitialized = true;
			return runtimeVersion;
		}

		Version GetVersion2() {
			try {
				var hash = GetHash(PathName);
				var info = GetVersionInfo(hash, versionInfo32);
				if (info != null)
					return info.Version;
				info = GetVersionInfo(hash, versionInfo64);
				if (info != null)
					return info.Version;
			}
			catch {
			}
			return null;
		}

		static VersionInfo GetVersionInfo(byte[] hash, VersionInfo[] infos) {
			foreach (var info in infos) {
				if (Equals(hash, info.Hash))
					return info;
			}
			return null;
		}

		static byte[] GetHash(string fullPath) {
			try {
				using (var hasher = MD5.Create()) {
					using (var outStream = new NullStream()) {
						using (var csStream = new CryptoStream(outStream, hasher, CryptoStreamMode.Write))
							new BinaryWriter(csStream).Write(File.ReadAllBytes(fullPath));
					}
					return hasher.Hash;
				}
			}
			catch {
			}
			return null;
		}

		static bool Equals(byte[] a, byte[] b) {
			if (a == null && b == null)
				return true;
			if (a == null || b == null)
				return false;
			if (a.Length != b.Length)
				return false;
			for (var i = 0; i < a.Length; i++) {
				if (a[i] != b[i])
					return false;
			}
			return true;
		}

		public override string ToString() {
			return PathName;
		}
	}
}
