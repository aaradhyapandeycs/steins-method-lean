import Foundation
import PDFKit

// Usage: swift pdftext.swift input.pdf  -> page texts separated by form feeds on stdout
let path = CommandLine.arguments[1]
guard let doc = PDFDocument(url: URL(fileURLWithPath: path)) else {
    FileHandle.standardError.write("cannot open \(path)\n".data(using: .utf8)!)
    exit(1)
}
for i in 0..<doc.pageCount {
    if let page = doc.page(at: i) {
        print(page.string ?? "")
        print("\u{0C}")
    }
}
