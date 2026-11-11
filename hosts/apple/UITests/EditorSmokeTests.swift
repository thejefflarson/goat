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
