import XCTest

final class EditorSmokeTests: XCTestCase {
    func testRunDrawsTheStarterProgram() {
        let app = XCUIApplication()
        app.launchArguments = ["-goat-ui-smoke"]
        app.launch()

        XCTAssertTrue(app.textViews["goat code"].waitForExistence(timeout: 30), "editor did not open")

        // By identifier: the web page also labels its own canvas "drawing".
        let canvas = app.otherElements["canvas"]
        XCTAssertTrue(canvas.waitForExistence(timeout: 30), "canvas missing")

        let run = app.buttons["Run"]
        wait(for: [expectation(for: NSPredicate(format: "isEnabled == true"), evaluatedWith: run)], timeout: 60)
        run.tap()

        wait(for: [expectation(for: NSPredicate(format: "value == 'finished'"), evaluatedWith: canvas)], timeout: 60)
        XCTAssertFalse(app.staticTexts.matching(NSPredicate(format: "label BEGINSWITH 'problem:'")).firstMatch.exists)
    }
}


/// Goes through the real document browser, with no `-goat-ui-smoke` shortcut: Create
/// Document must produce a file in local Documents and open the editor on it.
final class CreateDocumentTests: XCTestCase {
    func testCreateDocumentOpensTheEditor() {
        let app = XCUIApplication()
        app.launch()

        // The control is a button labelled "Create Document" on an empty browser and
        // "Add" in the navigation bar otherwise; accept either.
        let candidates = [
            app.buttons["Create Document"],
            app.navigationBars.buttons["Add"],
            app.buttons["Add"],
        ]
        let deadline = Date().addingTimeInterval(30)
        var create: XCUIElement?
        while create == nil, Date() < deadline {
            create = candidates.first { $0.exists && $0.isHittable }
            if create == nil { Thread.sleep(forTimeInterval: 0.5) }
        }
        guard let create else {
            attachTree(of: app, named: "browser without a create button")
            return XCTFail("no Create Document control in the browser")
        }
        create.tap()

        let editor = app.textViews["goat code"]
        if !editor.waitForExistence(timeout: 30) {
            attachTree(of: app, named: "after tapping create")
            XCTFail("the editor did not open after creating a document")
        }
    }

    private func attachTree(of app: XCUIApplication, named name: String) {
        let attachment = XCTAttachment(string: app.debugDescription)
        attachment.name = name
        attachment.lifetime = .keepAlways
        add(attachment)
        print("ELEMENT TREE (\(name)):\n\(app.debugDescription)")
    }
}
