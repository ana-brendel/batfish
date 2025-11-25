package org.batfish.minesweeper.question.verify;

import com.google.auto.service.AutoService;
import org.batfish.common.Answerer;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.plugin.Plugin;
import org.batfish.datamodel.questions.Question;

import org.batfish.question.QuestionPlugin;

/** QuestionPlugin for {@link VerifierQuestion}. */
@AutoService(Plugin.class)
public final class VerifierQuestionPlugin extends QuestionPlugin {
    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new VerifierAnswerer((VerifierQuestion) question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new VerifierQuestion();
    }
}