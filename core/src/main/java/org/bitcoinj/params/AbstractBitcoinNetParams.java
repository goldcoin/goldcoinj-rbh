/*
 * Copyright 2013 Google Inc.
 * Copyright 2015 Andreas Schildbach
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.bitcoinj.params;

import static com.google.common.base.Preconditions.checkState;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.concurrent.TimeUnit;

import com.google.common.base.Preconditions;
import org.bitcoinj.core.Block;
import org.bitcoinj.core.Coin;
import org.bitcoinj.core.NetworkParameters;
import org.bitcoinj.core.Sha256Hash;
import org.bitcoinj.core.StoredBlock;
import org.bitcoinj.core.Transaction;
import org.bitcoinj.core.Utils;
import org.bitcoinj.utils.MonetaryFormat;
import org.bitcoinj.core.VerificationException;
import org.bitcoinj.store.BlockStore;
import org.bitcoinj.store.BlockStoreException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.base.Stopwatch;

import org.bitcoinj.core.BitcoinSerializer;

/**
 * Parameters for Bitcoin-like networks.
 */
public abstract class AbstractBitcoinNetParams extends NetworkParameters {

    /**
     * Scheme part for Bitcoin URIs.
     */
    public static final String BITCOIN_SCHEME = "bitcoin";
    public static final int REWARD_HALVING_INTERVAL = 210000;

    private static final Logger log = LoggerFactory.getLogger(AbstractBitcoinNetParams.class);

    public AbstractBitcoinNetParams() {
        super();
    }

    /**
     * Checks if we are at a reward halving point.
     * @param height The height of the previous stored block
     * @return If this is a reward halving point
     */
    public final boolean isRewardHalvingPoint(final int height) {
        return ((height + 1) % REWARD_HALVING_INTERVAL) == 0;
    }

    /**
     * Checks if we are at a difficulty transition point.
     * @param height The height of the previous stored block
     * @return If this is a difficulty transition point
     */
    public final boolean isDifficultyTransitionPoint(final int height) {
        return ((height + 1) % this.getInterval()) == 0;
    }

    @Override
    public void checkDifficultyTransitions(final StoredBlock storedPrev, final Block nextBlock,
        final BlockStore blockStore) throws VerificationException, BlockStoreException {
        final Block prev = storedPrev.getHeader();

        if(storedPrev.getHeight() + 1 >= rbhHeight) {
            if(storedPrev.getHeight() + 1 <= rbhHeight + 240)
                return;

            GoldenRiver(storedPrev, nextBlock, blockStore);
            return;
        }

        // Is this supposed to be a difficulty transition point?
        if (!isDifficultyTransitionPoint(storedPrev.getHeight())) {

            // No ... so check the difficulty didn't actually change.
            if (nextBlock.getDifficultyTarget() != prev.getDifficultyTarget())
                throw new VerificationException("Unexpected change in difficulty at height " + storedPrev.getHeight() +
                        ": " + Long.toHexString(nextBlock.getDifficultyTarget()) + " vs " +
                        Long.toHexString(prev.getDifficultyTarget()));
            return;
        }

        // We need to find a block far back in the chain. It's OK that this is expensive because it only occurs every
        // two weeks after the initial block chain download.
        final Stopwatch watch = Stopwatch.createStarted();
        Sha256Hash hash = prev.getHash();
        StoredBlock cursor = null;
        final int interval = this.getInterval();
        for (int i = 0; i < interval; i++) {
            cursor = blockStore.get(hash);
            if (cursor == null) {
                // This should never happen. If it does, it means we are following an incorrect or busted chain.
                throw new VerificationException(
                        "Difficulty transition point but we did not find a way back to the last transition point. Not found: " + hash);
            }
            hash = cursor.getHeader().getPrevBlockHash();
        }
        checkState(cursor != null && isDifficultyTransitionPoint(cursor.getHeight() - 1),
                "Didn't arrive at a transition point.");
        watch.stop();
        if (watch.elapsed(TimeUnit.MILLISECONDS) > 50)
            log.info("Difficulty transition traversal took {}", watch);

        Block blockIntervalAgo = cursor.getHeader();
        int timespan = (int) (prev.getTimeSeconds() - blockIntervalAgo.getTimeSeconds());
        // Limit the adjustment step.
        final int targetTimespan = this.getTargetTimespan();
        if (timespan < targetTimespan / 4)
            timespan = targetTimespan / 4;
        if (timespan > targetTimespan * 4)
            timespan = targetTimespan * 4;

        BigInteger newTarget = Utils.decodeCompactBits(prev.getDifficultyTarget());
        newTarget = newTarget.multiply(BigInteger.valueOf(timespan));
        newTarget = newTarget.divide(BigInteger.valueOf(targetTimespan));

        if (newTarget.compareTo(this.getMaxTarget()) > 0) {
            log.info("Difficulty hit proof of work limit: {}", newTarget.toString(16));
            newTarget = this.getMaxTarget();
        }

        int accuracyBytes = (int) (nextBlock.getDifficultyTarget() >>> 24) - 3;
        long receivedTargetCompact = nextBlock.getDifficultyTarget();

        // The calculated difficulty is to a higher precision than received, so reduce here.
        BigInteger mask = BigInteger.valueOf(0xFFFFFFL).shiftLeft(accuracyBytes * 8);
        newTarget = newTarget.and(mask);
        long newTargetCompact = Utils.encodeCompactBits(newTarget);

        if (newTargetCompact != receivedTargetCompact)
            throw new VerificationException("Network provided difficulty bits do not match what was calculated: " +
                    Long.toHexString(newTargetCompact) + " vs " + Long.toHexString(receivedTargetCompact));
    }

    void GoldenRiver(StoredBlock storedPrev, Block nextBlock, BlockStore blockStore) {

        int height = storedPrev.getHeight() + 1;
        // Whether or not we had a massive difficulty fall authorized
        boolean didHalfAdjust = false;
        
        long averageTime = 120;
        final long nTargetTimespanCurrent = 2 * 60 * 60; // Two hours
        final long nTargetSpacingCurrent  = 2 * 60; // Two minutes
        long nInterval = nTargetTimespanCurrent / nTargetSpacingCurrent;



        // GoldCoin: This fixes an issue where a 51% attack can change difficulty at will.
        // Go back the full period unless it's the first retarget after genesis. Code courtesy of Art Forz
        long blockstogoback = nInterval - 1;

        if ((storedPrev.getHeight() + 1) != nInterval)
            blockstogoback = nInterval;

        StoredBlock pindexFirst = storedPrev;

        try {
            for (int i = 0; pindexFirst != null && i < blockstogoback; ++i)
                pindexFirst = pindexFirst.getPrev(blockStore);
            Preconditions.checkNotNull(pindexFirst);
        } catch (BlockStoreException x) {
            return;
        }

        //We need to set this in a way that reflects how fast blocks are actually being solved..
        //First we find the last 60 blocks and take the time between blocks
        //That gives us a list of 59 time differences
        //Then we take the median of those times and multiply it by 60 to get our actualtimespan
        // We want to limit the possible difficulty raise/fall over 60 and 240 blocks here
        // So we get the difficulty at 60 and 240 blocks ago

        StoredBlock tblock1 = storedPrev;//We want to copy storedPrev to avoid changing it accidentally

        StoredBlock tblock2 = tblock1;

        ArrayList<Long> last60BlockTimes = new ArrayList<>(60);

        ArrayList<Long> last120BlockTimes = new ArrayList<>(120);

        long nbits60ago = 0;
        long nbits240ago = 0;
        int counter = 0;
        while (counter <= 240)
        {
            if (counter == 60)
                nbits60ago = tblock2.getHeader().getDifficultyTarget();
            if (counter == 240)
                nbits240ago = tblock2.getHeader().getDifficultyTarget();

            if (last60BlockTimes.size() < 60)
                last60BlockTimes.add(tblock2.getHeader().getTimeSeconds());
            if ((last120BlockTimes.size() < 120))
                last120BlockTimes.add(tblock2.getHeader().getTimeSeconds());

            try {
                tblock2 = tblock2.getPrev(blockStore);
                if (tblock2 == null)
                    return;
            } catch (BlockStoreException x) {
                return;
            }
            ++counter;
        }



        ArrayList<Long> last59TimeDifferences = new ArrayList<>(59);
        ArrayList<Long> last119TimeDifferences = new ArrayList<>(119);
        long total = 0;
        int xy = 0;

        while (xy < 119)
        {
            if (xy < 59)
                last59TimeDifferences.add(Math.abs(last60BlockTimes.get(xy) - last60BlockTimes.get(xy + 1)));

            last119TimeDifferences.add(Math.abs(last120BlockTimes.get(xy) - last120BlockTimes.get(xy + 1)));
            total += last119TimeDifferences.get(xy);

            ++xy;
        }

        Collections.sort(last59TimeDifferences, new Comparator<Long>() {
            @Override
            public int compare(Long o1, Long o2) {
                return o1.compareTo(o2);
            }
        });

        //(BCLog::DIFFICULTY, "Median Time between blocks is: %d \n", last59TimeDifferences[29]);



        long nActualTimespan = Math.abs(last59TimeDifferences.get(29));
        long medTime = nActualTimespan;
        averageTime = total / 119;

        //LogPrint(BCLog::DIFFICULTY, "Average time between blocks: %d\n", averageTime);

        medTime = (medTime > averageTime) ? averageTime : medTime;

        if (averageTime >= 180 && last119TimeDifferences.get(0) >= 1200 && last119TimeDifferences.get(1) >= 1200)
        {
            didHalfAdjust = true;
            medTime = 240;
        }



        //Fixes an issue where median time between blocks is greater than 120 seconds and is not permitted to be lower by the defence system
        //Causing difficulty to drop without end
        if (medTime >= 120)
        {
            //Check to see whether we are in a deadlock situation with the 51% defense system
            int numTooClose = 0;
            int index = 1;

            while (index != 55)
            {
                if (Math.abs(last60BlockTimes.get(last60BlockTimes.size() - index) - last60BlockTimes.get(last60BlockTimes.size() - (index + 5))) == 600)
                {
                    ++numTooClose;
                }
                ++index;
            }

            if (numTooClose > 0)
            {
                //We found 6 blocks that were solved in exactly 10 minutes
                //Averaging 1.66 minutes per block
                //LogPrint(BCLog::DIFFICULTY, "DeadLock detected and fixed - Difficulty Increased\n");
                medTime = 119;
            }
            else
            {
                //LogPrint(BCLog::DIFFICULTY, "DeadLock not detected. \n");
            }
        }

        //216 == (int64) 180.0/100.0 * 120
        //122 == (int64) 102.0/100.0 * 120 == 122.4
        if (averageTime > 216 || medTime > 122)
        {
            if (didHalfAdjust)
            {
                // If the average time between blocks was
                // too high.. allow a dramatic difficulty
                // fall..
                medTime = (long)(120 * 142.0 / 100.0);
            }
            else
            {
                // Otherwise only allow a 120/119 fall per block
                // maximum.. As we now adjust per block..
                // 121 == (int64) 120 * 120.0/119.0
                medTime = 121;
            }
        }
        // 117 -- (int64) 120.0 * 98.0/100.0
        else if (averageTime < 117 || medTime < 117)
        {
            // If the average time between blocks is within 2% of target value
            // Or if the median time stamp between blocks is within 2% of the target value
            // Limit diff increase to 2%
            medTime = 117;
        }

        nActualTimespan = medTime * 60;
        //Now we get the old targets
        BigInteger bn60ago = Utils.decodeCompactBits(nbits60ago);
        BigInteger bn240ago = Utils.decodeCompactBits(nbits240ago);
        BigInteger bnLast = storedPrev.getHeader().getDifficultyTargetAsInteger(height);

        //Set the new target
        BigInteger bnNew = bnLast;

        bnNew = bnNew.multiply(BigInteger.valueOf(nActualTimespan));
        bnNew = bnNew.divide(BigInteger.valueOf(nTargetTimespanCurrent));

        // Set a floor on difficulty decreases per block(20% lower maximum
        // than the previous block difficulty).. when there was no halfing
        // necessary.. 10/8 == 1.0/0.8
        bnLast = bnLast.multiply(BigInteger.valueOf(10));
        bnLast = bnLast.divide(BigInteger.valueOf(8));

        if (!didHalfAdjust && bnNew.compareTo(bnLast) > 0)
            bnNew = bnLast;

        // Set ceilings on difficulty increases per block
        //1.0/1.02 == 100/102
        bn60ago = bn60ago.multiply(BigInteger.valueOf(100));
        bn60ago = bn60ago.divide(BigInteger.valueOf(102));

        if (bnNew.compareTo(bn60ago) < 0)
            bnNew = bn60ago;

        //1.0/(1.02*4) ==  100 / 408;
        bn240ago = bn240ago.multiply(BigInteger.valueOf(100));
        bn240ago = bn240ago.divide(BigInteger.valueOf(408));

        if (bnNew.compareTo(bn240ago) < 0)
            bnNew = bn240ago;

        //Sets a ceiling on highest target value (lowest possible difficulty)
        if (bnNew.compareTo(maxTargetScrypt) > 0)
            bnNew = maxTargetScrypt;


        verifyDifficulty(bnNew, nextBlock);
    }

    void verifyDifficulty(BigInteger newTarget, Block nextBlock) {
        int accuracyBytes = (int) (nextBlock.getDifficultyTarget() >>> 24) - 3;
        long receivedTargetCompact = nextBlock.getDifficultyTarget();
        BigInteger mask = BigInteger.valueOf(0xFFFFFFL).shiftLeft(accuracyBytes * 8);
        newTarget = newTarget.and(mask);
        long newTargetCompact = Utils.encodeCompactBits(newTarget);

        if (newTargetCompact != receivedTargetCompact)
            throw new VerificationException("Network provided difficulty bits do not match what was calculated: " +
                    Long.toHexString(newTargetCompact) + " vs " + Long.toHexString(receivedTargetCompact));

    }

    @Override
    public Coin getMaxMoney() {
        return MAX_MONEY;
    }

    @Override
    public Coin getMinNonDustOutput() {
        return Transaction.MIN_NONDUST_OUTPUT;
    }

    @Override
    public MonetaryFormat getMonetaryFormat() {
        return new MonetaryFormat();
    }

    @Override
    public int getProtocolVersionNum(final ProtocolVersion version) {
        return version.getBitcoinProtocolVersion();
    }

    @Override
    public BitcoinSerializer getSerializer(boolean parseRetain) {
        return new BitcoinSerializer(this, parseRetain);
    }

    @Override
    public String getUriScheme() {
        return BITCOIN_SCHEME;
    }

    @Override
    public boolean hasMaxMoney() {
        return true;
    }
}
